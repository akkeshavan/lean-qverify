"""
Example: verify the quantum teleportation circuit (pre-measurement unitary).

The full teleportation protocol includes classical communication and
post-measurement corrections; here we verify the unitary prefix.
"""

from qiskit import QuantumCircuit
from lean_qverify import verify_circuit


def main():
    # 3 qubits: q[0] = message, q[1] = Alice's Bell half, q[2] = Bob's half
    qc = QuantumCircuit(3, name="teleport-prep")

    # Step 1: Create Bell pair on q[1], q[2]
    qc.h(1)
    qc.cx(1, 2)

    # Step 2: Alice encodes
    qc.cx(0, 1)
    qc.h(0)

    print("Teleportation circuit (pre-measurement):")
    print(qc.draw(output="text"))
    print()

    result = verify_circuit(qc)
    print(result)


if __name__ == "__main__":
    main()
