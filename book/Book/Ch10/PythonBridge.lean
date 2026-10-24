import LeanQVerify.QASM.ParseTheorems

/-!
# Chapter 10 — The Python Bridge

Read `prose.md` in this directory alongside this file.

This file shows the Lean side of the Python bridge:
the QASM program type and the well-formedness theorems.
-/

open LeanQVerify QASM

-- ── 1. The QASMProgram type ───────────────────────────────────────────────────

-- A QASM program in the library is:
--   { registers : List RegisterDecl, gates : List GateApp, warnings : List String }
#check QASMProgram

-- ── 2. GateApp: parsed gate applications ─────────────────────────────────────

-- GateApp is an inductive type with one constructor per supported gate.
-- Each constructor takes qubit references.
#check GateApp

-- A qubit reference is a register name + index
#check QubitRef   -- { reg : String, idx : Nat }

-- ── 3. Well-formedness ────────────────────────────────────────────────────────

-- A program is well-formed if every qubit reference is within bounds.
-- This is expressed as a Prop:
#check @QASMProgram.wellFormed   -- QASMProgram → Prop

-- And as a Bool checker (decidable):
#check @QASMProgram.checkWellFormed  -- QASMProgram → Bool

-- ── 4. Soundness: Bool checker implies Prop ───────────────────────────────────

-- The main theorem connecting the checker to the predicate:
#check @checkWellFormed_sound
-- prog.checkWellFormed = true → prog.wellFormed

-- This says: if the Bool checker passes, the formal predicate holds.
-- The proof goes through List.all_eq_true and the per-gate checker.

-- ── 5. Concrete programs ─────────────────────────────────────────────────────

-- The Bell program (H on q[0], CNOT on q[0] and q[1]):
#check @bellProgram_wellFormed
-- ({registers := [⟨"q", 2⟩], gates := [.h ⟨"q",0⟩, .cx ⟨"q",0⟩ ⟨"q",1⟩],
--   warnings := []}).checkWellFormed = true

-- The GHZ-3 program:
#check @ghz3Program_wellFormed

-- These are proved by rfl: the Bool checker reduces to true by computation.

-- ── 6. A negative example ────────────────────────────────────────────────────

-- The parser rejects programs where a gate references a qubit out of bounds.
-- badProgram_fails proves that the checker returns false for such a program.
#check @badProgram_fails
