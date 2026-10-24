import LeanQVerify.Circuit.QCircuit
import LeanQVerify.Spec.StandardSpecs

/-!
# Chapter 5 — Circuits

Read `prose.md` in this directory alongside this file.
-/

open LeanQVerify QCircuit CircuitSpec

-- ── 1. The Bell circuit ───────────────────────────────────────────────────────

-- The library already defines bellPrep. Let's look at it.
#print bellPrep

-- Equivalent definition showing the structure:
def myBell : QCircuit 2 :=
  .cons (.H   ⟨0, by norm_num⟩)
  (.cons (.CNOT ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)
   .empty)

-- ── 2. Gate count ─────────────────────────────────────────────────────────────

-- .size counts all gates
example : myBell.size = 2 := by decide

-- countGates with a predicate counts matching gates
example : countGates (fun g => match g with | .CNOT _ _ => true | _ => false) myBell = 1 := by
  simp [countGates, myBell]

-- ── 3. Appending circuits ─────────────────────────────────────────────────────

def myH : QCircuit 2 := .ofGate (.H ⟨0, by norm_num⟩)
def myCNOT : QCircuit 2 := .ofGate (.CNOT ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)

-- myH ++ myCNOT has the same structure as myBell
example : (myH ++ myCNOT).size = 2 := by decide

-- ── 4. Circuit equivalence ────────────────────────────────────────────────────

-- The ≅ relation: two circuits implement the same unitary
#check @QCircuit.equiv   -- QCircuit n → QCircuit n → Prop
-- c₁ ≅ c₂ means c₁.denote = c₂.denote

-- Every circuit is equivalent to itself
example : myBell ≅ myBell := rfl

-- ── 5. Applying a circuit to a state vector ───────────────────────────────────

-- applyTo c v = c.denote.mulVec v
#check @QCircuit.applyTo  -- QCircuit n → (Fin (2^n) → ℂ) → (Fin (2^n) → ℂ)
