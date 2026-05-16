"""
Numerical counterexample search using Qiskit Aer.

When Lean reports a spec violation (or a sorry-backed proof cannot be trusted),
this module tries to find a concrete input state that demonstrates the failure.
It uses the GPU-aware simulator selector for large circuits.
"""

from __future__ import annotations

import logging
import numpy as np
from typing import Optional

from .result import CounterExample
from .simulator import get_simulator, unitary_simulator

logger = logging.getLogger(__name__)


def extract_unitary(qc) -> Optional[np.ndarray]:
    """
    Extract the unitary matrix of a Qiskit QuantumCircuit.
    Returns None on failure (e.g., circuit contains measurements).
    """
    try:
        from qiskit import transpile  # type: ignore
        sim = unitary_simulator()
        t = transpile(qc, sim)
        job = sim.run(t)
        result = job.result()
        return np.array(result.get_unitary(t))
    except Exception as exc:
        logger.debug("Unitary extraction failed: %s", exc)
        return None


def check_equivalence(
    qc1,
    qc2,
    n_qubits: int,
    atol: float = 1e-6,
) -> Optional[CounterExample]:
    """
    Check if two Qiskit circuits are numerically equivalent.

    Extracts their unitaries and compares. If they differ, constructs a
    CounterExample using the standard basis state that shows the largest
    discrepancy.

    Returns None if equivalent, or a CounterExample otherwise.
    """
    U1 = extract_unitary(qc1)
    U2 = extract_unitary(qc2)

    if U1 is None or U2 is None:
        logger.warning("Could not extract unitaries for equivalence check")
        return None

    diff = np.abs(U1 - U2)
    if np.max(diff) <= atol:
        return None

    # Find the basis column with largest deviation
    col_norms = np.sum(diff, axis=0)
    worst_col = int(np.argmax(col_norms))
    worst_row = int(np.argmax(diff[:, worst_col]))

    input_label  = _basis_label(worst_col, n_qubits)
    expected_amp = complex(U2[worst_row, worst_col])
    actual_amp   = complex(U1[worst_row, worst_col])
    output_label = _basis_label(worst_row, n_qubits)

    return CounterExample(
        input_state=input_label,
        expected=f"amplitude of {output_label} = {expected_amp:.4f}",
        actual=f"amplitude of {output_label} = {actual_amp:.4f}",
        note=f"max column deviation = {np.max(diff):.6f}",
    )


def check_measurement_prob(
    qc,
    input_state_index: int,
    qubit_index: int,
    outcome: bool,
    expected_prob: float,
    n_qubits: int,
    atol: float = 1e-4,
) -> Optional[CounterExample]:
    """
    Check whether the circuit gives at least `expected_prob` for measuring
    `outcome` on `qubit_index`, starting from `input_state_index`.

    Returns None if the spec is satisfied, or a CounterExample if not.
    """
    U = extract_unitary(qc)
    if U is None:
        return None

    dim = 2 ** n_qubits
    psi_in = np.zeros(dim, dtype=complex)
    psi_in[input_state_index] = 1.0
    psi_out = U @ psi_in

    # Sum probability over all basis states where bit `qubit_index` == outcome
    actual_prob = 0.0
    for k in range(dim):
        bit = (k >> qubit_index) & 1
        if bool(bit) == outcome:
            actual_prob += abs(psi_out[k]) ** 2

    if actual_prob >= expected_prob - atol:
        return None

    return CounterExample(
        input_state=_basis_label(input_state_index, n_qubits),
        expected=f"P(q{qubit_index}={'1' if outcome else '0'}) >= {expected_prob:.4f}",
        actual=f"P(q{qubit_index}={'1' if outcome else '0'}) = {actual_prob:.4f}",
    )


def _basis_label(index: int, n_qubits: int) -> str:
    """Format a basis state index as a ket, e.g. |010>."""
    bits = format(index, f"0{n_qubits}b")
    return f"|{bits}>"
