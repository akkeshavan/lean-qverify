OPENQASM 3;
include "stdgates.inc";
qubit[2] q;
ry(0.5) q[0];
ry(0.5) q[1];
cx q[0], q[1];
ry(1.0) q[0];
