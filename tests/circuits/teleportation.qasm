OPENQASM 3;
include "stdgates.inc";
// Quantum teleportation — unitary prefix (pre-measurement).
// Qubits: q[0] = Alice's message qubit, q[1] = Alice's Bell half,
//         q[2] = Bob's Bell half.
qubit[3] q;
// Step 1: create Bell pair on q[1], q[2]
h q[1];
cx q[1], q[2];
// Step 2: Alice's encoding
cx q[0], q[1];
h q[0];
