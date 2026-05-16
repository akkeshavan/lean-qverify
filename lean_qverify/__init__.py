"""
lean-qverify: Formal verification of quantum circuits.

Connects Qiskit circuits to a Lean 4 formal verifier via OpenQASM 3.
"""

from .bridge import verify_circuit
from .runner import verify_qasm_file, cli_main
from .result import VerifyResult, Verdict, CounterExample
from .gpu import detect_gpu, should_use_gpu, GPUInfo

__all__ = [
    "verify_circuit",
    "verify_qasm_file",
    "cli_main",
    "VerifyResult",
    "Verdict",
    "CounterExample",
    "detect_gpu",
    "should_use_gpu",
    "GPUInfo",
]

__version__ = "0.1.0"
