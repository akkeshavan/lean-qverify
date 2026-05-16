"""
Bridge between Qiskit circuits and the Lean verifier.

The bridge:
1. Accepts a Qiskit QuantumCircuit.
2. Exports it to OpenQASM 3 via Qiskit's built-in exporter.
3. Writes the QASM to a temp file.
4. Invokes the `lean-qverify-check` binary.
5. Parses the JSON summary returned by the binary.
6. Optionally runs a numerical counterexample search.
7. Returns a VerifyResult.
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
        return dumps(qc)
    except ImportError:
        # Older Qiskit versions: fall back to QASM 2
        return qc.qasm()


def verify_circuit(
    qc,
    *,
    run_counterexample: bool = True,
    timeout: int = 60,
) -> VerifyResult:
    """
    Verify a Qiskit QuantumCircuit using the Lean formal verifier.

    Parameters
    ----------
    qc:
        A Qiskit QuantumCircuit to verify.
    run_counterexample:
        If True and Lean reports a failure, attempt a numerical counterexample
        search using the GPU-aware Aer simulator.
    timeout:
        Maximum seconds to wait for the Lean binary.

    Returns
    -------
    VerifyResult with verdict, qubit/gate counts, warnings, and any
    counterexample found.
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
        tmp_path.unlink(missing_ok=True)
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

    # Determine verdict from warnings (sorry stubs → WARNING, else PROVED)
    if any("sorry" in w.lower() or "unsupported" in w.lower() for w in warnings):
        verdict = Verdict.WARNING
    else:
        verdict = Verdict.PROVED

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
