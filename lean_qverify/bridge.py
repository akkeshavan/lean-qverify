"""
Bridge between Qiskit circuits and the Lean verifier.

The bridge has two modes:

  parse mode (default):
    Calls lean-qverify-check to parse and elaborate the circuit.
    Returns Verdict.PARSED — the circuit is well-formed but no spec has been
    kernel-checked.  This is NOT a proof.

  prove mode (via verify_circuit_spec):
    Calls lean-qverify-check --prove with a CircuitSpec.
    Generates a Lean theorem file and invokes Lean's kernel.
    Returns Verdict.STRUCT_PROVED (structural spec kernel-checked) or
    Verdict.PROVED (semantic spec kernel-checked), or Verdict.FAILED.
"""

from __future__ import annotations

import json
import logging
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Optional

from .result import VerifyResult, Verdict

logger = logging.getLogger(__name__)

# Name of the compiled Lean binary (must be on PATH or set via LEAN_QVERIFY_BIN env var)
_DEFAULT_BIN = "lean-qverify-check"


def _find_binary() -> Optional[Path]:
    import os
    env_path = os.environ.get("LEAN_QVERIFY_BIN")
    if env_path:
        p = Path(env_path)
        if p.is_file():
            return p
    found = shutil.which(_DEFAULT_BIN)
    return Path(found) if found else None


def _circuit_to_qasm(qc) -> str:
    """Export a Qiskit circuit to an OpenQASM 3 string."""
    try:
        from qiskit.qasm3 import dumps  # type: ignore
    except ImportError:
        raise ImportError(
            "qiskit.qasm3 not found. lean-qverify requires Qiskit >= 1.0. "
            "Install with: pip install qiskit>=1.0"
        ) from None
    return dumps(qc)


def verify_circuit(
    qc,
    *,
    run_counterexample: bool = True,
    timeout: int = 60,
) -> VerifyResult:
    """
    Parse and elaborate a Qiskit QuantumCircuit via the Lean verifier.

    This function parses the circuit and returns structural information
    (qubit count, gate count, warnings).  The verdict will be
    ``Verdict.PARSED`` — the circuit is well-formed but no specification
    has been kernel-checked.

    To kernel-check a formal specification, use ``verify_circuit_spec``.

    Parameters
    ----------
    qc:
        A Qiskit QuantumCircuit to parse.
    run_counterexample:
        If True and parsing reports warnings, attempt a numerical
        counterexample search using the GPU-aware Aer simulator.
    timeout:
        Maximum seconds to wait for the Lean binary.

    Returns
    -------
    VerifyResult with verdict PARSED (or WARNING/ERROR), qubit/gate counts,
    warnings, and any counterexample found.
    """
    binary = _find_binary()
    if binary is None:
        return VerifyResult(
            verdict=Verdict.ERROR,
            error_msg=(
                f"'{_DEFAULT_BIN}' not found on PATH. "
                "Build it with: cd lean-qverify && lake build lean-qverify-check"
            ),
        )

    qasm_source = _circuit_to_qasm(qc)

    with tempfile.NamedTemporaryFile(suffix=".qasm", mode="w",
                                     delete=False) as f:
        f.write(qasm_source)
        tmp_path = Path(f.name)

    try:
        proc = subprocess.run(
            [str(binary), str(tmp_path)],
            capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return VerifyResult(
            verdict=Verdict.ERROR,
            error_msg=f"lean-qverify-check timed out after {timeout}s",
        )
    finally:
        tmp_path.unlink(missing_ok=True)

    lean_output = proc.stdout + proc.stderr

    if proc.returncode == 2:
        return VerifyResult(
            verdict=Verdict.ERROR,
            lean_output=lean_output,
            error_msg="lean-qverify-check: file read error",
        )

    # Parse JSON summary from stdout
    try:
        summary = json.loads(proc.stdout.strip())
    except (json.JSONDecodeError, ValueError):
        return VerifyResult(
            verdict=Verdict.ERROR,
            lean_output=lean_output,
            error_msg="lean-qverify-check returned non-JSON output",
        )

    n_qubits  = summary.get("nQubits", 0)
    n_gates   = summary.get("nGates",  0)
    warnings  = summary.get("warnings", [])

    # Parse-only path: circuit was elaborated but no spec was kernel-checked.
    # Report PARSED (not PROVED — nothing has been proved yet).
    # WARNING if any gate angle is unrecognised (semantic proofs would use sorry)
    # or if any gate was skipped (unsupported syntax).
    _warning_keywords = ("not a recognised", "unsupported gate skipped")
    if any(any(kw in w for kw in _warning_keywords) for w in warnings):
        verdict = Verdict.WARNING
    else:
        verdict = Verdict.PARSED

    result = VerifyResult(
        verdict=verdict,
        n_qubits=n_qubits,
        n_gates=n_gates,
        warnings=warnings,
        lean_output=lean_output,
    )

    # Optionally search for a numerical counterexample on warning/failure
    if run_counterexample and verdict in (Verdict.FAILED, Verdict.WARNING):
        result.counterexample = _search_counterexample(qc, n_qubits)

    return result


def verify_circuit_spec(
    qc,
    spec,
    *,
    timeout: int = 120,
) -> VerifyResult:
    """
    Kernel-check a structural specification for a Qiskit QuantumCircuit.

    This is the genuine verification path: Lean's kernel checks a theorem
    about the imported circuit against the supplied spec.

    Parameters
    ----------
    qc:
        A Qiskit QuantumCircuit.
    spec:
        A ``StructuralSpec`` (gate count, CNOT count, depth, RZ count).
        Import from ``lean_qverify.prover``.
    timeout:
        Seconds to wait for Lean's kernel.

    Returns
    -------
    VerifyResult with verdict STRUCT_PROVED (kernel-checked) or FAILED.
    """
    from .prover import verify_structural_spec, StructuralSpec

    if not isinstance(spec, StructuralSpec):
        return VerifyResult(
            verdict=Verdict.ERROR,
            error_msg="spec must be a StructuralSpec instance",
        )

    check_bin = _find_binary()
    if check_bin is None:
        return VerifyResult(
            verdict=Verdict.ERROR,
            error_msg="lean-qverify-check not found",
        )

    qasm_source = _circuit_to_qasm(qc)

    proved, log = verify_structural_spec(
        qasm_source, spec, timeout=timeout,
        check_bin=check_bin,
    )

    return VerifyResult(
        verdict=Verdict.STRUCT_PROVED if proved else Verdict.FAILED,
        lean_output=log,
    )


def _search_counterexample(qc, n_qubits: int):
    """Try to find a numerical counterexample for the circuit."""
    try:
        from .counterexample import check_measurement_prob
        # Spot-check: measure qubit 0 from |0...0> input
        ce = check_measurement_prob(
            qc,
            input_state_index=0,
            qubit_index=0,
            outcome=False,
            expected_prob=0.0,   # trivially satisfied; real checks need spec data
            n_qubits=n_qubits,
        )
        return ce
    except Exception as exc:
        logger.debug("Counterexample search failed: %s", exc)
        return None
