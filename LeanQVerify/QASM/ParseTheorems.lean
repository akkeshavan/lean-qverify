import LeanQVerify.QASM.Parser

/-!
# Formal Properties of the QASM Parser

This module provides a **formal correctness specification** for the QASM parser:

1. `GateApp.qubitRefs` — extract all qubit references from a parsed gate
2. `QASMProgram.wellFormed` — formal predicate: every non-skipped gate's qubit
   references are within the bounds declared in the register map
3. `QASMProgram.checkWellFormed` — computable (`Bool`) well-formedness checker
4. `checkWellFormed_sound` — kernel-checked soundness: the Boolean checker
   implies the formal predicate (the checker never misses a violation)
5. Concrete well-formedness theorems for standard circuit programs

Together these constitute a **verified specification layer**: any program
accepted by `checkWellFormed` satisfies the formal `wellFormed` property,
and this implication is kernel-checked by Lean's type theory.
-/

namespace LeanQVerify.QASM

-- ---------------------------------------------------------------------------
-- 1. qubitRefs: extract all QubitRef values from a parsed gate
-- ---------------------------------------------------------------------------

/-- All qubit references mentioned by a parsed gate application. -/
def GateApp.qubitRefs (g : GateApp) : List QubitRef :=
  match g with
  | .h    q          => [q]
  | .x    q          => [q]
  | .y    q          => [q]
  | .z    q          => [q]
  | .s    q          => [q]
  | .t    q          => [q]
  | .rx   _ q        => [q]
  | .ry   _ q        => [q]
  | .rz   _ q        => [q]
  | .cx   c1 c2      => [c1, c2]
  | .cz   c1 c2      => [c1, c2]
  | .swap q1 q2      => [q1, q2]
  | .ccx  c1 c2 c3   => [c1, c2, c3]
  | .u3   _ _ _ q    => [q]
  | .ch   c1 c2      => [c1, c2]
  | .cy   c1 c2      => [c1, c2]
  | .cp   _ c1 c2    => [c1, c2]
  | .crz  _ c1 c2    => [c1, c2]
  | .rzz  _ q1 q2    => [q1, q2]
  | .rxx  _ q1 q2    => [q1, q2]
  | .ryy  _ q1 q2    => [q1, q2]
  | .skipped _       => []

-- A `skipped` gate has no qubit references.
@[simp]
theorem qubitRefs_skipped (s : String) : (GateApp.skipped s).qubitRefs = [] := rfl

-- ---------------------------------------------------------------------------
-- 2. wellFormed: formal predicate for valid programs
-- ---------------------------------------------------------------------------

/-- A parsed gate is well-formed w.r.t. a register list if every qubit reference
    it mentions corresponds to a declared register with a large-enough size. -/
def GateApp.wellFormedFor (regs : List RegDecl) (g : GateApp) : Prop :=
  ∀ q ∈ g.qubitRefs,
    ∃ r ∈ regs, r.name = q.reg ∧ q.index < r.size

/-- A program is well-formed if every gate (including skipped ones — which have
    no qubit refs — vacuously) is well-formed for the declared registers. -/
def QASMProgram.wellFormed (prog : QASMProgram) : Prop :=
  ∀ g ∈ prog.gates, g.wellFormedFor prog.registers

-- Skipped gates are vacuously well-formed.
theorem skipped_wellFormed (regs : List RegDecl) (s : String) :
    (GateApp.skipped s).wellFormedFor regs := by
  simp [GateApp.wellFormedFor, qubitRefs_skipped]

-- ---------------------------------------------------------------------------
-- 3. checkWellFormed: computable checker (Bool)
-- ---------------------------------------------------------------------------

/-- Computable well-formedness check for a single gate. -/
def checkGateWF (regs : List RegDecl) (g : GateApp) : Bool :=
  g.qubitRefs.all (fun q =>
    regs.any (fun r => r.name == q.reg && decide (q.index < r.size)))

/-- Computable well-formedness check for a full program. -/
def QASMProgram.checkWellFormed (prog : QASMProgram) : Bool :=
  prog.gates.all (checkGateWF prog.registers)

-- ---------------------------------------------------------------------------
-- 4. Soundness: checkWellFormed → wellFormed
-- ---------------------------------------------------------------------------

/-- Soundness of the checker for a single gate:
    if `checkGateWF regs g = true` then every qubit ref in g is valid. -/
theorem checkGateWF_sound {regs : List RegDecl} {g : GateApp}
    (h : checkGateWF regs g = true) :
    g.wellFormedFor regs := by
  intro q hq
  simp only [checkGateWF, List.all_eq_true] at h
  have hqb := h q hq
  simp only [List.any_eq_true] at hqb
  obtain ⟨r, hr, hcheck⟩ := hqb
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨hname, hlt⟩ := hcheck
  exact ⟨r, hr, (beq_iff_eq.mp hname), (of_decide_eq_true hlt)⟩

/-- Soundness of the full checker:
    if `prog.checkWellFormed = true` then every gate in the program is well-formed. -/
theorem checkWellFormed_sound {prog : QASMProgram}
    (h : prog.checkWellFormed = true) : prog.wellFormed := by
  intro g hg
  simp only [QASMProgram.checkWellFormed, List.all_eq_true] at h
  exact checkGateWF_sound (h g hg)

-- ---------------------------------------------------------------------------
-- 5. Concrete well-formedness theorems (kernel-checked)
-- ---------------------------------------------------------------------------

/-- A Bell state program (2-qubit register, H + CX) is well-formed. -/
theorem bellProgram_wellFormed :
    ({ registers := [⟨"q", 2⟩]
       gates     := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩]
       warnings  := [] } : QASMProgram).checkWellFormed = true := by rfl

/-- A GHZ-3 program is well-formed. -/
theorem ghz3Program_wellFormed :
    ({ registers := [⟨"q", 3⟩]
       gates     := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩, .cx ⟨"q", 0⟩ ⟨"q", 2⟩]
       warnings  := [] } : QASMProgram).checkWellFormed = true := by rfl

/-- Corollary: the Bell program satisfies the formal well-formedness predicate. -/
theorem bellProgram_wellFormed_prop :
    ({ registers := [⟨"q", 2⟩]
       gates     := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩]
       warnings  := [] } : QASMProgram).wellFormed :=
  checkWellFormed_sound bellProgram_wellFormed

/-- Corollary: the GHZ-3 program satisfies the formal well-formedness predicate. -/
theorem ghz3Program_wellFormed_prop :
    ({ registers := [⟨"q", 3⟩]
       gates     := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩, .cx ⟨"q", 0⟩ ⟨"q", 2⟩]
       warnings  := [] } : QASMProgram).wellFormed :=
  checkWellFormed_sound ghz3Program_wellFormed

/-- A program with an out-of-bounds qubit reference is rejected by the checker. -/
theorem badProgram_fails :
    ({ registers := [⟨"q", 1⟩]
       gates     := [.cx ⟨"q", 0⟩ ⟨"q", 1⟩]  -- qubit 1 out of bounds for size-1 register
       warnings  := [] } : QASMProgram).checkWellFormed = false := by rfl

end LeanQVerify.QASM
