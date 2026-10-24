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

/-!
## Angle recognition

Qiskit exports rotation angles as Float.  We recognise rational multiples of π
with denominators 1, 2, 3, 4, 6, 8, 12 — covering all standard gate angles:
T (π/4), S (π/2), Sdg (−π/2), Tdg (−π/4), CX-phase (π), common RZ angles.

Recognised angles produce exact `ℝ` expressions (no sorry).
Unrecognised floats fall through to `sorry` (with a warning from the caller).

`angleIsRecognised` is computable (Float only).
`floatToReal` is noncomputable (returns ℝ).
-/

/-- Float equality within ε=1e-9. Internal QASM utility used by `floatToReal` and the serializer. -/
def floatEq (a b : Float) : Bool := (a - b).abs < 1e-9

/-- Float approximation of π. Internal QASM utility; prefer `Real.pi` in Lean proofs. -/
def fpi : Float := 3.141592653589793238

/-- Computable check: is θ a recognised rational multiple of π? -/
def angleIsRecognised (θ : Float) : Bool :=
  let ratios : List Float :=
    [ 0, 1, -1, 0.5, -0.5, 1.0/3, -1.0/3, 0.25, -0.25,
      2.0/3, -2.0/3, 0.75, -0.75, 1.0/6, -1.0/6,
      0.125, -0.125, 0.375, -0.375, 0.625, -0.625, 0.875, -0.875,
      1.0/12, -1.0/12, 5.0/12, -5.0/12,
      2.0, -2.0, 1.5, -1.5 ]
  ratios.any fun r => floatEq θ (r * fpi)

/-- Convert a Float angle to ℝ.
    Recognises common rational multiples of π exactly.
    Falls back to 0 for unrecognised values; callers emit a warning.
    Returning 0 is sound for structural proofs (gate count, depth) since those
    pattern-match on constructors, not angle values. -/
noncomputable def floatToReal (θ : Float) : ℝ :=
  if floatEq θ 0.0           then 0
  else if floatEq θ fpi      then Real.pi
  else if floatEq θ (-fpi)   then -Real.pi
  else if floatEq θ (fpi/2)  then Real.pi / 2
  else if floatEq θ (-fpi/2) then -(Real.pi / 2)
  else if floatEq θ (fpi/3)  then Real.pi / 3
  else if floatEq θ (-fpi/3) then -(Real.pi / 3)
  else if floatEq θ (fpi/4)  then Real.pi / 4
  else if floatEq θ (-fpi/4) then -(Real.pi / 4)
  else if floatEq θ (2*fpi/3)  then 2 * Real.pi / 3
  else if floatEq θ (-2*fpi/3) then -(2 * Real.pi / 3)
  else if floatEq θ (3*fpi/4)  then 3 * Real.pi / 4
  else if floatEq θ (-3*fpi/4) then -(3 * Real.pi / 4)
  else if floatEq θ (fpi/6)  then Real.pi / 6
  else if floatEq θ (-fpi/6) then -(Real.pi / 6)
  else if floatEq θ (fpi/8)  then Real.pi / 8
  else if floatEq θ (-fpi/8) then -(Real.pi / 8)
  else if floatEq θ (3*fpi/8)  then 3 * Real.pi / 8
  else if floatEq θ (-3*fpi/8) then -(3 * Real.pi / 8)
  else if floatEq θ (5*fpi/8)  then 5 * Real.pi / 8
  else if floatEq θ (-5*fpi/8) then -(5 * Real.pi / 8)
  else if floatEq θ (7*fpi/8)  then 7 * Real.pi / 8
  else if floatEq θ (-7*fpi/8) then -(7 * Real.pi / 8)
  else if floatEq θ (fpi/12)   then Real.pi / 12
  else if floatEq θ (-fpi/12)  then -(Real.pi / 12)
  else if floatEq θ (5*fpi/12) then 5 * Real.pi / 12
  else if floatEq θ (-5*fpi/12) then -(5 * Real.pi / 12)
  else if floatEq θ (2*fpi)   then 2 * Real.pi
  else if floatEq θ (-2*fpi)  then -(2 * Real.pi)
  else if floatEq θ (3*fpi/2)  then 3 * Real.pi / 2
  else if floatEq θ (-3*fpi/2) then -(3 * Real.pi / 2)
  else 0  -- unrecognised angle: return 0 (callers emit a warning; structural proofs are unaffected)

-- ---------------------------------------------------------------------------
-- Register map: name → (startIndex, size)
-- ---------------------------------------------------------------------------

/-- Maps register names to their base qubit offset and size. -/
abbrev RegMap := List (String × Nat × Nat)  -- (name, start, size)

-- Internal to the QASM subsystem (used by Elaborator + Serializer); not stable library API.
def buildRegMap (regs : List RegDecl) : RegMap :=
  let rec go (rs : List RegDecl) (offset : Nat) : RegMap :=
    match rs with
    | []      => []
    | r :: rest =>
      (r.name, offset, r.size) :: go rest (offset + r.size)
  go regs 0

def totalQubits (regs : List RegDecl) : Nat :=
  regs.foldl (fun acc r => acc + r.size) 0

def resolveQubit (m : RegMap) (ref : QubitRef) : Option Nat :=
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
  | .rx θ q =>
    let (ok, w) := resolve1qubit q
    let warn := if ok && !angleIsRecognised θ
                then some s!"rx angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                else w
    (ok, warn)
  | .ry θ q =>
    let (ok, w) := resolve1qubit q
    let warn := if ok && !angleIsRecognised θ
                then some s!"ry angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                else w
    (ok, warn)
  | .rz θ q =>
    let (ok, w) := resolve1qubit q
    let warn := if ok && !angleIsRecognised θ
                then some s!"rz angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                else w
    (ok, warn)
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
  | .u3 θ φ lam q =>
    let (ok, w) := resolve1qubit q
    let warn := if ok && (!angleIsRecognised θ || !angleIsRecognised φ || !angleIsRecognised lam)
                then some "u3 angle not a recognised rational multiple of π; semantic proofs will use sorry"
                else w
    (ok, warn)
  | .ch  c t =>
    match resolve2 c t with | some _ => (true, none) | none => (false, some "unresolved qubits for ch")
  | .cy  c t =>
    match resolve2 c t with | some _ => (true, none) | none => (false, some "unresolved qubits for cy")
  | .cp  θ c t =>
    match resolve2 c t with
    | some _ =>
      let warn := if !angleIsRecognised θ
                  then some s!"cp angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                  else none
      (true, warn)
    | none => (false, some "unresolved qubits for cp")
  | .crz θ c t =>
    match resolve2 c t with
    | some _ =>
      let warn := if !angleIsRecognised θ
                  then some s!"crz angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                  else none
      (true, warn)
    | none => (false, some "unresolved qubits for crz")
  | .rzz θ i j =>
    match resolve2 i j with
    | some _ =>
      let warn := if !angleIsRecognised θ
                  then some s!"rzz angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                  else none
      (true, warn)
    | none => (false, some "unresolved qubits for rzz")
  | .rxx θ i j =>
    match resolve2 i j with
    | some _ =>
      let warn := if !angleIsRecognised θ
                  then some s!"rxx angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                  else none
      (true, warn)
    | none => (false, some "unresolved qubits for rxx")
  | .ryy θ i j =>
    match resolve2 i j with
    | some _ =>
      let warn := if !angleIsRecognised θ
                  then some s!"ryy angle {θ} not a recognised rational multiple of π; semantic proofs will use sorry"
                  else none
      (true, warn)
    | none => (false, some "unresolved qubits for ryy")
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
  | .u3   θ φ lam q => match resolve1 q with
    | some i =>
      let warn := if !angleIsRecognised θ || !angleIsRecognised φ || !angleIsRecognised lam
                  then some "u3 angle not a recognised rational multiple of π; using sorry"
                  else none
      (some (.U3 (floatToReal θ) (floatToReal φ) (floatToReal lam) i), warn)
    | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .ch   c t     => match resolve2 c t with | some (ci, ti) => (some (.CH  ci ti), none) | none => (none, some "unresolved qubits for ch")
  | .cy   c t     => match resolve2 c t with | some (ci, ti) => (some (.CY  ci ti), none) | none => (none, some "unresolved qubits for cy")
  | .cp   θ c t   => match resolve2 c t with
    | some (ci, ti) =>
      let warn := if !angleIsRecognised θ then some s!"cp angle {θ} not a recognised rational multiple of π; using sorry" else none
      (some (.CP (floatToReal θ) ci ti), warn)
    | none => (none, some "unresolved qubits for cp")
  | .crz  θ c t   => match resolve2 c t with
    | some (ci, ti) =>
      let warn := if !angleIsRecognised θ then some s!"crz angle {θ} not a recognised rational multiple of π; using sorry" else none
      (some (.CRZ (floatToReal θ) ci ti), warn)
    | none => (none, some "unresolved qubits for crz")
  | .rzz  θ i j   => match resolve2 i j with
    | some (ii, ji) =>
      let warn := if !angleIsRecognised θ then some s!"rzz angle {θ} not a recognised rational multiple of π; using sorry" else none
      (some (.RZZ (floatToReal θ) ii ji), warn)
    | none => (none, some "unresolved qubits for rzz")
  | .rxx  θ i j   => match resolve2 i j with
    | some (ii, ji) =>
      let warn := if !angleIsRecognised θ then some s!"rxx angle {θ} not a recognised rational multiple of π; using sorry" else none
      (some (.RXX (floatToReal θ) ii ji), warn)
    | none => (none, some "unresolved qubits for rxx")
  | .ryy  θ i j   => match resolve2 i j with
    | some (ii, ji) =>
      let warn := if !angleIsRecognised θ then some s!"ryy angle {θ} not a recognised rational multiple of π; using sorry" else none
      (some (.RYY (floatToReal θ) ii ji), warn)
    | none => (none, some "unresolved qubits for ryy")
  | .rx   θ q     => match resolve1 q with
    | some i =>
      let warn := if angleIsRecognised θ then none
                  else some s!"rx angle {θ} not a recognised rational multiple of π; using sorry"
      (some (.RX (floatToReal θ) i), warn)
    | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .ry   θ q     => match resolve1 q with
    | some i =>
      let warn := if angleIsRecognised θ then none
                  else some s!"ry angle {θ} not a recognised rational multiple of π; using sorry"
      (some (.RY (floatToReal θ) i), warn)
    | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
  | .rz   θ q     => match resolve1 q with
    | some i =>
      let warn := if angleIsRecognised θ then none
                  else some s!"rz angle {θ} not a recognised rational multiple of π; using sorry"
      (some (.RZ (floatToReal θ) i), warn)
    | none => (none, some s!"unresolved qubit {q.reg}[{q.index}]")
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
