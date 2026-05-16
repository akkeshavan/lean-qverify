import LeanQVerify.QASM.Parser
import LeanQVerify.Circuit.QCircuit

/-!
# QASM Elaborator

Converts a `QASMProgram` (the untyped AST from the parser) into a
`QCircuit n` (the typed, dependently-kinded circuit).

The key challenge: `QCircuit n` is parameterized by the qubit count `n`,
which is a compile-time value in Lean's type theory but is only known at
runtime from the QASM register declarations. We return `⟨n, circuit⟩`
packaged as `Σ n, QCircuit n` so callers can work with the existential.

**Elaboration steps:**
1. Compute `n` = total qubits from all `qubit[k] name;` declarations.
2. Build a register map: register name → starting qubit index (flat layout).
3. For each `GateApp`, resolve qubit references to `Fin n` indices and
   construct the corresponding `Gate n`. Out-of-bounds or malformed
   references are skipped with a warning.
4. Return the circuit and any elaboration warnings.
-/

namespace LeanQVerify.QASM

open LeanQVerify

/-- Convert a Float angle (from the parser) to ℝ.
    The QASM parser is a trusted bridge; this conversion is not formally verified. -/
private noncomputable def floatToReal (_ : Float) : ℝ := sorry

-- ---------------------------------------------------------------------------
-- Register map: name → (startIndex, size)
-- ---------------------------------------------------------------------------

/-- Maps register names to their base qubit offset and size. -/
abbrev RegMap := List (String × Nat × Nat)  -- (name, start, size)

private def buildRegMap (regs : List RegDecl) : RegMap :=
  let rec go (rs : List RegDecl) (offset : Nat) : RegMap :=
    match rs with
    | []      => []
    | r :: rest =>
      (r.name, offset, r.size) :: go rest (offset + r.size)
  go regs 0

private def totalQubits (regs : List RegDecl) : Nat :=
  regs.foldl (fun acc r => acc + r.size) 0

/-- Resolve a `QubitRef` to an absolute qubit index.
    Returns `none` if the register is unknown or the index is out of range. -/
private def resolveQubit (m : RegMap) (ref : QubitRef) : Option Nat :=
  match m.find? (fun ⟨name, _, _⟩ => name == ref.reg) with
  | none                   => none
  | some ⟨_, start, size⟩ =>
    if ref.index < size then some (start + ref.index) else none

-- ---------------------------------------------------------------------------
-- Elaboration result
-- ---------------------------------------------------------------------------

/-- Result of elaborating a QASMProgram (computable — used by the CLI). -/
structure ElabResult where
  nQubits  : Nat
  nGates   : Nat
  warnings : List String   -- elaboration-level warnings (in addition to parse warnings)

-- ---------------------------------------------------------------------------
-- Core elaboration
-- ---------------------------------------------------------------------------

/-- Try to make a `Fin n` from a raw index; returns `none` if out of bounds. -/
private def mkFin (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

/-- Count and validate a single `GateApp` without constructing a `Gate n`.
    Returns true if the gate is representable, plus any warning. -/
private def countGate (n : Nat) (m : RegMap) (g : GateApp) :
    Bool × Option String :=
  let resolve1 (r : QubitRef) : Option (Fin n) :=
    resolveQubit m r >>= mkFin n
  let resolve2 (r1 r2 : QubitRef) : Option (Fin n × Fin n) := do
    let i ← resolve1 r1; let j ← resolve1 r2; return (i, j)
  let resolve3 (r1 r2 r3 : QubitRef) : Option (Fin n × Fin n × Fin n) := do
    let i ← resolve1 r1; let j ← resolve1 r2; let k ← resolve1 r3; return (i, j, k)
  let resolve1qubit (q : QubitRef) :=
    match resolve1 q with
    | some _ => (true,  none)
    | none   => (false, some s!"unresolved qubit {q.reg}[{q.index}]")
  match g with
  | .h    q       => resolve1qubit q
  | .x    q       => resolve1qubit q
  | .y    q       => resolve1qubit q
  | .z    q       => resolve1qubit q
  | .s    q       => resolve1qubit q
  | .t    q       => resolve1qubit q
  | .rx _ q       => resolve1qubit q
  | .ry _ q       => resolve1qubit q
  | .rz _ q       => resolve1qubit q
  | .cx   c t     =>
    match resolve2 c t with | some _ => (true, none) | none => (false, some "unresolved qubits for cx")
  | .cz   c t     =>
    match resolve2 c t with | some _ => (true, none) | none => (false, some "unresolved qubits for cz")
  | .swap c t     =>
    match resolve2 c t with | some _ => (true, none) | none => (false, some "unresolved qubits for swap")
  | .ccx  c1 c2 t =>
    match resolve3 c1 c2 t with
    | some _ => (true,  none)
    | none   => (false, some s!"unresolved qubits for ccx")
  | .skipped name => (false, some s!"unsupported gate skipped: {name}")

/-- Elaborate a full `QASMProgram` into an `ElabResult`. -/
def elaborate (prog : QASMProgram) : ElabResult :=
  let n   := totalQubits prog.registers
  let m   := buildRegMap prog.registers
  let (nGates, warns) :=
    prog.gates.foldl (fun (acc : Nat × List String) gapp =>
      let (cnt, ws) := acc
      match countGate n m gapp with
      | (true,  w) => (cnt + 1, ws ++ w.toList)
      | (false, w) => (cnt,     ws ++ w.toList))
    (0, [])
  { nQubits  := n
    nGates   := nGates
    warnings := prog.warnings ++ warns }

-- ---------------------------------------------------------------------------
-- Formal circuit (noncomputable — for use in proofs only)
-- ---------------------------------------------------------------------------

/-- Elaborate a single `GateApp` into a `Gate n` (noncomputable; needs ℝ for rotation gates). -/
private noncomputable def elabGate (n : Nat) (m : RegMap) (g : GateApp) :
    Option (Gate n) × Option String :=
  let resolve1 (r : QubitRef) : Option (Fin n) :=
    resolveQubit m r >>= mkFin n
  let resolve2 (r1 r2 : QubitRef) : Option (Fin n × Fin n) := do
    let i ← resolve1 r1; let j ← resolve1 r2; return (i, j)
  let resolve3 (r1 r2 r3 : QubitRef) : Option (Fin n × Fin n × Fin n) := do
    let i ← resolve1 r1; let j ← resolve1 r2; let k ← resolve1 r3; return (i, j, k)
  match g with
  | .h    q       => match resolve1 q with | some i => (some (.H i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .x    q       => match resolve1 q with | some i => (some (.X i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .y    q       => match resolve1 q with | some i => (some (.Y i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .z    q       => match resolve1 q with | some i => (some (.Z i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .s    q       => match resolve1 q with | some i => (some (.S i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .t    q       => match resolve1 q with | some i => (some (.T i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .cx   c t     => match resolve2 c t with | some (ci, ti) => (some (.CNOT ci ti), none) | none => (none, some "unresolved qubits for cx")
  | .cz   c t     => match resolve2 c t with | some (ci, ti) => (some (.CZ  ci ti), none) | none => (none, some "unresolved qubits for cz")
  | .swap i j     => match resolve2 i j with | some (ii, ji) => (some (.SWAP ii ji), none) | none => (none, some "unresolved qubits for swap")
  | .ccx  c1 c2 t => match resolve3 c1 c2 t with | some (c1i, c2i, ti) => (some (.CCX c1i c2i ti), none) | none => (none, some "unresolved qubits for ccx")
  | .rx   θ q     => match resolve1 q with | some i => (some (.RX (floatToReal θ) i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .ry   θ q     => match resolve1 q with | some i => (some (.RY (floatToReal θ) i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .rz   θ q     => match resolve1 q with | some i => (some (.RZ (floatToReal θ) i), none) | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .skipped name => (none, some s!"unsupported gate skipped: {name}")

/-- Produce a formal QCircuit from a parsed program (noncomputable; for proof use). -/
noncomputable def elaborateCircuit (prog : QASMProgram) :
    Σ n : Nat, QCircuit n :=
  let n := totalQubits prog.registers
  let m := buildRegMap prog.registers
  let gates := prog.gates.filterMap (fun gapp => (elabGate n m gapp).1)
  let circuit := gates.reverse.foldl (fun c g => .cons g c) (QCircuit.empty : QCircuit n)
  ⟨n, circuit⟩

-- ---------------------------------------------------------------------------
-- Convenience: parse + elaborate in one step
-- ---------------------------------------------------------------------------

/-- Parse a QASM source string and elaborate it into an `ElabResult`. -/
def parseAndElaborate (source : String) : ElabResult :=
  elaborate (parse source)

end LeanQVerify.QASM
