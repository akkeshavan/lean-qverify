"""
Shared pytest fixtures for lean-qverify Python tests.
"""

import pytest
from pathlib import Path

CIRCUITS_DIR = Path(__file__).parent.parent / "circuits"


@pytest.fixture
def bell_qasm_path():
    return CIRCUITS_DIR / "bell.qasm"


@pytest.fixture
def ghz_qasm_path():
    return CIRCUITS_DIR / "ghz.qasm"


@pytest.fixture
def teleportation_qasm_path():
    return CIRCUITS_DIR / "teleportation.qasm"


@pytest.fixture
def bell_circuit():
    """A Qiskit Bell state preparation circuit."""
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(2)
    qc.h(0)
    qc.cx(0, 1)
    return qc


@pytest.fixture
def ghz_circuit():
    """A Qiskit 3-qubit GHZ preparation circuit."""
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(3)
    qc.h(0)
    qc.cx(0, 1)
    qc.cx(0, 2)
    return qc
