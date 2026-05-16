"""
Tests for the Qiskit → Lean bridge.

Tests that don't need the Lean binary exercise the QASM export and
result parsing. Tests that call verify_circuit are skipped when the
lean-qverify-check binary is not on PATH.
"""

import pytest
import shutil
from lean_qverify.result import Verdict, VerifyResult, CounterExample


LEAN_BIN_AVAILABLE = shutil.which("lean-qverify-check") is not None

skip_no_lean = pytest.mark.skipif(
    not LEAN_BIN_AVAILABLE,
    reason="lean-qverify-check binary not found on PATH"
)


# ---------------------------------------------------------------------------
# Result type tests (no binary needed)
# ---------------------------------------------------------------------------

def test_verify_result_ok_proved():
    r = VerifyResult(verdict=Verdict.PROVED, n_qubits=2, n_gates=2)
    assert r.ok is True


def test_verify_result_not_ok_failed():
    r = VerifyResult(verdict=Verdict.FAILED)
    assert r.ok is False


def test_verify_result_str_includes_verdict():
    r = VerifyResult(verdict=Verdict.WARNING, n_qubits=3, n_gates=3,
                     warnings=["sorry stub"])
    s = str(r)
    assert "warning" in s.lower()
    assert "sorry stub" in s


def test_counterexample_str():
    ce = CounterExample(input_state="|00>", expected="p=0.5", actual="p=0.3")
    r = VerifyResult(verdict=Verdict.FAILED, counterexample=ce)
    s = str(r)
    assert "|00>" in s


# ---------------------------------------------------------------------------
# QASM export (Qiskit needed)
# ---------------------------------------------------------------------------

def test_qasm_export_bell(bell_circuit):
    pytest.importorskip("qiskit")
    from lean_qverify.bridge import _circuit_to_qasm
    qasm = _circuit_to_qasm(bell_circuit)
    assert "h" in qasm.lower() or "H" in qasm
    assert "cx" in qasm.lower() or "CX" in qasm


# ---------------------------------------------------------------------------
# Bridge integration (Lean binary needed)
# ---------------------------------------------------------------------------

@skip_no_lean
def test_verify_bell_circuit(bell_circuit):
    from lean_qverify import verify_circuit
    result = verify_circuit(bell_circuit, run_counterexample=False)
    assert result.n_qubits == 2
    assert result.n_gates == 2
    assert result.verdict in (Verdict.PROVED, Verdict.WARNING)


@skip_no_lean
def test_verify_ghz_circuit(ghz_circuit):
    from lean_qverify import verify_circuit
    result = verify_circuit(ghz_circuit, run_counterexample=False)
    assert result.n_qubits == 3
    assert result.n_gates == 3


@skip_no_lean
def test_verify_qasm_file_bell(bell_qasm_path):
    from lean_qverify import verify_qasm_file
    result = verify_qasm_file(bell_qasm_path, run_counterexample=False)
    assert result.n_qubits == 2


def test_verify_qasm_file_missing():
    from lean_qverify import verify_qasm_file
    result = verify_qasm_file("/nonexistent/path/circuit.qasm")
    assert result.verdict == Verdict.ERROR
    assert "not found" in result.error_msg.lower()


def test_verify_circuit_no_binary(bell_circuit):
    """Without the Lean binary, expect an ERROR result, not an exception."""
    import os
    original = os.environ.get("LEAN_QVERIFY_BIN")
    os.environ["LEAN_QVERIFY_BIN"] = "/nonexistent/lean-qverify-check"
    try:
        from lean_qverify import verify_circuit
        result = verify_circuit(bell_circuit, run_counterexample=False)
        assert result.verdict == Verdict.ERROR
    finally:
        if original is None:
            del os.environ["LEAN_QVERIFY_BIN"]
        else:
            os.environ["LEAN_QVERIFY_BIN"] = original
