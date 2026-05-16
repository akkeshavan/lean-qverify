"""
High-level runner: verify a QASM file or Qiskit circuit from the command line
or programmatically.
"""

from __future__ import annotations

import logging
import sys
from pathlib import Path

logger = logging.getLogger(__name__)


def verify_qasm_file(path: str | Path, **kwargs) -> "VerifyResult":
    """
    Verify a QASM file directly (bypasses Qiskit export).

    Parses the QASM, converts to a minimal Qiskit circuit for
    counterexample search, then runs the Lean verifier.
    """
    from .result import VerifyResult, Verdict

    path = Path(path)
    if not path.exists():
        return VerifyResult(
            verdict=Verdict.ERROR,
            error_msg=f"File not found: {path}",
        )

    source = path.read_text()

    # Build a minimal Qiskit circuit from QASM for counterexample purposes
    qc = _qasm_to_qiskit(source)
    if qc is None:
        return VerifyResult(
            verdict=Verdict.ERROR,
            error_msg=f"Could not parse QASM file '{path}' with Qiskit",
        )

    from .bridge import verify_circuit
    return verify_circuit(qc, **kwargs)


def _qasm_to_qiskit(source: str):
    """Parse a QASM source string into a Qiskit QuantumCircuit."""
    try:
        from qiskit.qasm3 import loads  # type: ignore
        return loads(source)
    except Exception:
        pass
    try:
        from qiskit import QuantumCircuit  # type: ignore
        return QuantumCircuit.from_qasm_str(source)
    except Exception as exc:
        logger.debug("Qiskit QASM parse failed: %s", exc)
        return None


def cli_main() -> None:
    """Entry point for `lean-qverify-build` console script."""
    import argparse

    logging.basicConfig(level=logging.WARNING,
                        format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="lean-qverify-build",
        description="Verify a quantum circuit (QASM file) using lean-qverify",
    )
    parser.add_argument("qasm_file", help="Path to an OpenQASM 3 file")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Show detailed output")
    parser.add_argument("--no-counterexample", action="store_true",
                        help="Skip numerical counterexample search")
    parser.add_argument("--timeout", type=int, default=60,
                        help="Timeout in seconds for Lean verifier (default: 60)")
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    result = verify_qasm_file(
        args.qasm_file,
        run_counterexample=not args.no_counterexample,
        timeout=args.timeout,
    )

    print(result)
    sys.exit(0 if result.ok else 1)
