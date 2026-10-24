OPENQASM 3;
include "stdgates.inc";
qubit[2] q;
rz(0.7853981633974483) q[0];
rz(0.7853981633974483) q[1];
cx q[0], q[1];
