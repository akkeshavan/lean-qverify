"""
Example: verify the Bell state preparation circuit.

Demonstrates the basic lean-qverify workflow:
  1. Build a Qiskit circuit.
  2. Call verify_circuit().
  3. Inspect the VerifyResult.
"""

from qiskit import QuantumCircuit
from lean_qverify import verify_circuit


def main():
    # Build the Bell state circuit: H on qubit 0, then CNOT 0→1
    qc = QuantumCircuit(2, name="bell")
    qc.h(0)
    qc.cx(0, 1)

    print("Circuit:")
    print(qc.draw(output="text"))
    print()

    result = verify_circuit(qc)
    print(result)


if __name__ == "__main__":
    main()
