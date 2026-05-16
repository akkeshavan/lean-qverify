"""
Example: verify a 2-qubit Grover search (1 iteration, target |11>).

Structure:
  - Equal superposition: H⊗H
  - Oracle: CZ (flips phase of |11>)
  - Diffusion: H⊗H, X⊗X, CZ, X⊗X, H⊗H

After 1 iteration on N=4 states with 1 marked state, the target
|11> has probability 1.0 (exact for this special case).
"""

from qiskit import QuantumCircuit
from lean_qverify import verify_circuit
from lean_qverify.counterexample import check_measurement_prob
from lean_qverify.simulator import get_simulator
import numpy as np


def build_grover_circuit() -> QuantumCircuit:
    qc = QuantumCircuit(2, name="grover-1iter")

    # Equal superposition
    qc.h(0)
    qc.h(1)

    # Oracle: mark |11>
    qc.cz(0, 1)

    # Diffusion operator
    qc.h(0)
    qc.h(1)
    qc.x(0)
    qc.x(1)
    qc.cz(0, 1)
    qc.x(0)
    qc.x(1)
    qc.h(0)
    qc.h(1)

    return qc


def main():
    qc = build_grover_circuit()
    print("Grover 1-iteration circuit (2 qubits, target |11>):")
    print(qc.draw(output="text"))
    print()

    # Formal verification via Lean
    result = verify_circuit(qc)
    print("Lean verification result:")
    print(result)
    print()

    # Numerical check: P(q1=1, q0=1) should be ~1.0
    ce = check_measurement_prob(
        qc,
        input_state_index=0,   # start from |00>
        qubit_index=0,
        outcome=True,          # expect bit 0 to be 1
        expected_prob=0.99,
        n_qubits=2,
    )
    if ce is None:
        print("Numerical check passed: P(q0=1) >= 0.99")
    else:
        print(f"Numerical check found discrepancy: {ce}")


if __name__ == "__main__":
    main()
