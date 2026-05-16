import LeanQVerify.QASM.Elaborator

/-!
# Elaborator unit tests

Tests that the QASM elaborator correctly converts parsed programs into
typed `QCircuit n` values. Uses `#guard` for elaboration-time checking.
-/

open LeanQVerify.QASM LeanQVerify

-- ---------------------------------------------------------------------------
-- Helper: elaborate a QASM string and inspect the result
-- ---------------------------------------------------------------------------

private def elabStr (src : String) : ElabResult :=
  parseAndElaborate src

-- ---------------------------------------------------------------------------
-- Qubit count
-- ---------------------------------------------------------------------------

#guard (elabStr "qubit[2] q;\nh q[0];").nQubits = 2
#guard (elabStr "qubit[3] q;").nQubits = 3

-- Two registers: total qubits = sum of sizes
#guard (elabStr "qubit[2] a;\nqubit[3] b;").nQubits = 5

-- ---------------------------------------------------------------------------
-- Gate count (via circuit size)
-- ---------------------------------------------------------------------------

#guard (elabStr "qubit[2] q;\nh q[0];\ncx q[0], q[1];").nGates = 2
#guard (elabStr "qubit[3] q;\nh q[0];\ncx q[0], q[1];\ncx q[0], q[2];").nGates = 3
#guard (elabStr "qubit[1] q;").nGates = 0   -- no gates

-- ---------------------------------------------------------------------------
-- Empty program
-- ---------------------------------------------------------------------------

#guard (elabStr "OPENQASM 3;").nQubits = 0
#guard (elabStr "OPENQASM 3;").nGates = 0

-- ---------------------------------------------------------------------------
-- Unsupported gate produces a warning, circuit still elaborates
-- ---------------------------------------------------------------------------

private def withUnsupported := "qubit[1] q;\nmygate q[0];\nh q[0];"

#guard (elabStr withUnsupported).nGates = 1   -- only h elaborated
#guard (elabStr withUnsupported).warnings.length ≥ 1

-- ---------------------------------------------------------------------------
-- Bell state elaboration
-- ---------------------------------------------------------------------------

private def bellElab := elabStr "qubit[2] q;\nh q[0];\ncx q[0], q[1];"

#guard bellElab.nQubits = 2
#guard bellElab.nGates = 2
#guard bellElab.warnings.isEmpty

-- ---------------------------------------------------------------------------
-- GHZ state elaboration
-- ---------------------------------------------------------------------------

private def ghzElab := elabStr "qubit[3] q;\nh q[0];\ncx q[0], q[1];\ncx q[0], q[2];"

#guard ghzElab.nQubits = 3
#guard ghzElab.nGates = 3
#guard ghzElab.warnings.isEmpty

-- ---------------------------------------------------------------------------
-- Multi-register: flat qubit indexing
-- ---------------------------------------------------------------------------

-- Two 2-qubit registers: a[0]=0, a[1]=1, b[0]=2, b[1]=3
private def multiReg := elabStr "qubit[2] a;\nqubit[2] b;\ncx a[0], b[0];"

#guard multiReg.nQubits = 4
#guard multiReg.nGates = 1
