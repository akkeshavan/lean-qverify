OPENQASM 3;
include "stdgates.inc";
qubit[2] q;
cx q[0], q[1];
cx q[1], q[0];
cx q[0], q[1];
