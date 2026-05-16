OPENQASM 3;
include "stdgates.inc";
qubit[3] q;
h q[1];
cx q[1], q[2];
cx q[0], q[1];
h q[0];
