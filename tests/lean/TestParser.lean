import LeanQVerify.QASM.Parser

/-!
# Parser unit tests

These tests exercise the QASM parser directly using `#eval` and `#guard`.
They run at elaboration time (no `lake test` required — just `lake build`
or opening the file in VS Code will check them).
-/

open LeanQVerify.QASM

-- ---------------------------------------------------------------------------
-- Helper: parse and extract gate count
-- ---------------------------------------------------------------------------

private def gateCount (src : String) : Nat :=
  (parse src).gates.length

private def regCount (src : String) : Nat :=
  (parse src).registers.length

private def warnCount (src : String) : Nat :=
  (parse src).warnings.length

-- ---------------------------------------------------------------------------
-- Header and include are silently ignored
-- ---------------------------------------------------------------------------

#guard gateCount "OPENQASM 3;\ninclude \"stdgates.inc\";\nqubit[1] q;\nh q[0];" = 1
#guard regCount  "OPENQASM 3;\nqubit[2] q;" = 1

-- ---------------------------------------------------------------------------
-- Register declarations
-- ---------------------------------------------------------------------------

#guard regCount "qubit[3] q;" = 1
#guard (parse "qubit[3] q;").registers[0]?.map (·.size) = some 3
#guard (parse "qubit[3] q;").registers[0]?.map (·.name) = some "q"

#guard regCount "qubit[2] a;\nqubit[3] b;" = 2
#guard (parse "qubit[2] a;\nqubit[3] b;").registers[1]?.map (·.name) = some "b"

-- ---------------------------------------------------------------------------
-- Single-qubit gates
-- ---------------------------------------------------------------------------

#guard gateCount "qubit[1] q;\nh q[0];"    = 1
#guard gateCount "qubit[1] q;\nx q[0];"    = 1
#guard gateCount "qubit[1] q;\ny q[0];"    = 1
#guard gateCount "qubit[1] q;\nz q[0];"    = 1
#guard gateCount "qubit[1] q;\ns q[0];"    = 1
#guard gateCount "qubit[1] q;\nt q[0];"    = 1

-- Check that parsed gate type matches
private def isHGate_q0 : Bool :=
  match (parse "qubit[1] q;\nh q[0];").gates[0]? with
  | some (GateApp.h ⟨"q", 0⟩) => true | _ => false
#guard isHGate_q0

private def isXGate_q0 : Bool :=
  match (parse "qubit[1] q;\nx q[0];").gates[0]? with
  | some (GateApp.x ⟨"q", 0⟩) => true | _ => false
#guard isXGate_q0

-- ---------------------------------------------------------------------------
-- Two-qubit gates
-- ---------------------------------------------------------------------------

#guard gateCount "qubit[2] q;\ncx q[0], q[1];"   = 1
#guard gateCount "qubit[2] q;\ncnot q[0], q[1];" = 1  -- alias
#guard gateCount "qubit[2] q;\ncz q[0], q[1];"   = 1
#guard gateCount "qubit[2] q;\nswap q[0], q[1];" = 1

private def isCxGate_q01 : Bool :=
  match (parse "qubit[2] q;\ncx q[0], q[1];").gates[0]? with
  | some (GateApp.cx ⟨"q", 0⟩ ⟨"q", 1⟩) => true | _ => false
#guard isCxGate_q01

-- ---------------------------------------------------------------------------
-- Three-qubit gate
-- ---------------------------------------------------------------------------

#guard gateCount "qubit[3] q;\nccx q[0], q[1], q[2];" = 1

private def isCcxGate_q012 : Bool :=
  match (parse "qubit[3] q;\nccx q[0], q[1], q[2];").gates[0]? with
  | some (GateApp.ccx ⟨"q", 0⟩ ⟨"q", 1⟩ ⟨"q", 2⟩) => true | _ => false
#guard isCcxGate_q012

-- ---------------------------------------------------------------------------
-- Rotation gates with angle parameters
-- ---------------------------------------------------------------------------

#guard gateCount "qubit[1] q;\nrx(1.5707963) q[0];" = 1
#guard gateCount "qubit[1] q;\nry(pi) q[0];"         = 1
#guard gateCount "qubit[1] q;\nrz(pi/2) q[0];"       = 1
#guard gateCount "qubit[1] q;\nrz(pi*0.5) q[0];"     = 1
#guard gateCount "qubit[1] q;\nrz(-pi/4) q[0];"      = 1

-- Verify pi/2 is parsed as approximately 1.5708
private def rzPiHalfAngle : Option Float :=
  match (parse "qubit[1] q;\nrz(pi/2) q[0];").gates[0]? with
  | some (GateApp.rz θ _) => some θ
  | _ => none
#guard rzPiHalfAngle.any (fun θ => θ > 1.57 && θ < 1.58)

-- ---------------------------------------------------------------------------
-- Multiple gates in sequence
-- ---------------------------------------------------------------------------

#guard gateCount "qubit[2] q;\nh q[0];\ncx q[0], q[1];" = 2
#guard gateCount "qubit[3] q;\nh q[0];\ncx q[0], q[1];\ncx q[0], q[2];" = 3

-- ---------------------------------------------------------------------------
-- Multiple registers with different names
-- ---------------------------------------------------------------------------

private def multiReg := "qubit[2] a;\nqubit[2] b;\ncx a[0], b[1];"

#guard regCount multiReg = 2
#guard gateCount multiReg = 1
private def isMultiRegCx : Bool :=
  match (parse multiReg).gates[0]? with
  | some (GateApp.cx ⟨"a", 0⟩ ⟨"b", 1⟩) => true | _ => false
#guard isMultiRegCx

-- ---------------------------------------------------------------------------
-- Unsupported constructs produce warnings, not failures
-- ---------------------------------------------------------------------------

-- Classical bit declaration is silently ignored
#guard gateCount "bit c;\nqubit[1] q;\nh q[0];" = 1
#guard warnCount "bit c;\nqubit[1] q;\nh q[0];" = 0  -- bit is explicitly ignored

-- Unknown gate → skipped warning
#guard warnCount "qubit[1] q;\nmygate q[0];" = 1
#guard gateCount "qubit[1] q;\nmygate q[0];" = 0  -- skipped gate not in list

-- ---------------------------------------------------------------------------
-- Line comments are ignored
-- ---------------------------------------------------------------------------

#guard gateCount "// Bell state\nqubit[2] q;\nh q[0]; // Hadamard\ncx q[0], q[1];" = 2

-- ---------------------------------------------------------------------------
-- Bell state from file-like string
-- ---------------------------------------------------------------------------

private def bellSrc :=
  "OPENQASM 3;\ninclude \"stdgates.inc\";\nqubit[2] q;\nh q[0];\ncx q[0], q[1];"

#guard regCount  bellSrc = 1
#guard gateCount bellSrc = 2
#guard warnCount bellSrc = 0
#guard (parse bellSrc).registers[0]?.map (·.size) = some 2
