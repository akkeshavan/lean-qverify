import LeanQVerify.Circuit.QCircuit
import LeanQVerify.Spec.CircuitSpec
import LeanQVerify.Spec.Satisfies

/-!
# Circuit and spec unit tests

Tests for QCircuit structural properties and CircuitSpec satisfaction.
All proofs here are checkable by `simp` — no `sorry` required.
-/

open LeanQVerify QCircuit CircuitSpec

-- ---------------------------------------------------------------------------
-- size
-- ---------------------------------------------------------------------------

#guard (QCircuit.empty : QCircuit 2).size = 0

example : (QCircuit.empty : QCircuit 3).size = 0 := rfl

example : (QCircuit.cons (.H 0) (QCircuit.empty : QCircuit 2)).size = 1 := rfl

example : bellPrep.size = 2 := rfl

example : ghzPrep.size = 3 := rfl

-- ---------------------------------------------------------------------------
-- append / size
-- ---------------------------------------------------------------------------

example : (bellPrep ++ (QCircuit.id : QCircuit 2)).size = bellPrep.size + (QCircuit.id : QCircuit 2).size := by
  simp [QCircuit.size, append, QCircuit.id]

-- Single gate append
example (n : ℕ) (g : Gate n) (c : QCircuit n) :
    (QCircuit.cons g c).size = c.size + 1 := by
  simp [QCircuit.size]; omega

-- ---------------------------------------------------------------------------
-- denote_empty
-- ---------------------------------------------------------------------------

example (n : ℕ) : (QCircuit.empty : QCircuit n).denote = 1 := denote_empty

-- ---------------------------------------------------------------------------
-- Gate count specifications (proved by simp)
-- ---------------------------------------------------------------------------

example : bellPrep ⊨ .gateCount (fun _ => true) 2 := by
  simp [satisfies, countGates, bellPrep]

example : ghzPrep ⊨ .gateCount (fun _ => true) 3 := by
  simp [satisfies, countGates, ghzPrep]

-- Empty circuit has 0 gates
example (n : ℕ) (pred : Gate n → Bool) :
    (QCircuit.empty : QCircuit n) ⊨ .gateCount pred 0 := by
  simp [satisfies, countGates]

-- Single H gate has count 1 for the all-true predicate
example (n : ℕ) (i : Fin n) :
    (QCircuit.ofGate (.H i)) ⊨ .gateCount (fun _ => true) 1 := by
  simp [satisfies, ofGate, countGates]

-- ---------------------------------------------------------------------------
-- Depth / maxDepth specifications
-- ---------------------------------------------------------------------------

example : bellPrep ⊨ .maxDepth 2 := by
  show depth bellPrep ≤ 2; native_decide

example : ghzPrep ⊨ .maxDepth 3 := by
  show depth ghzPrep ≤ 3; native_decide

-- ---------------------------------------------------------------------------
-- Conjunction
-- ---------------------------------------------------------------------------

example : bellPrep ⊨ .both (.gateCount (fun _ => true) 2) (.maxDepth 2) := by
  constructor
  · simp [satisfies, countGates, bellPrep]
  · show depth bellPrep ≤ 2; native_decide

-- ---------------------------------------------------------------------------
-- Satisfies lemmas from Satisfies.lean
-- ---------------------------------------------------------------------------

-- empty satisfies identity
example : (QCircuit.empty : QCircuit 2) ⊨ CircuitSpec.isIdentity 2 := by
  unfold satisfies isIdentity
  simp [denote_empty]

-- gate count monotonicity
example : bellPrep ⊨ .gateCount (fun _ => true) 5 := by
  apply satisfies_gateCount_mono bellPrep _ 2 5 (by norm_num)
  simp [satisfies, countGates, bellPrep]
