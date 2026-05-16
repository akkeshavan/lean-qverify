import LeanQVerify.Spec.CircuitSpec

/-!
# Satisfaction Lemmas

General lemmas about the `satisfies` (⊨) relation:
  - Monotonicity (weaker specs are easier to satisfy)
  - Conjunction introduction/elimination
  - Equivalence implies unitary equality
  - Empty circuit satisfies identity spec
-/

namespace LeanQVerify

open QCircuit CircuitSpec

-- ---------------------------------------------------------------------------
-- Basic structural lemmas
-- ---------------------------------------------------------------------------

/-- The empty circuit satisfies the identity spec. -/
theorem empty_satisfies_identity (n : ℕ) :
    (QCircuit.empty : QCircuit n) ⊨ CircuitSpec.isIdentity n := by
  unfold satisfies isIdentity
  simp [denote_empty]

/-- If a circuit satisfies both parts of a conjunction, it satisfies the conjunction. -/
theorem satisfies_both {n : ℕ} (c : QCircuit n) (s₁ s₂ : CircuitSpec n)
    (h₁ : c ⊨ s₁) (h₂ : c ⊨ s₂) : c ⊨ .both s₁ s₂ := ⟨h₁, h₂⟩

/-- Eliminate left conjunct. -/
theorem satisfies_both_left {n : ℕ} (c : QCircuit n) (s₁ s₂ : CircuitSpec n)
    (h : c ⊨ .both s₁ s₂) : c ⊨ s₁ := h.1

/-- Eliminate right conjunct. -/
theorem satisfies_both_right {n : ℕ} (c : QCircuit n) (s₁ s₂ : CircuitSpec n)
    (h : c ⊨ .both s₁ s₂) : c ⊨ s₂ := h.2

-- ---------------------------------------------------------------------------
-- Equivalence and matrix specs
-- ---------------------------------------------------------------------------

/-- Circuit equivalence implies implementing the same matrix. -/
theorem equiv_imp_sameMatrix {n : ℕ} (c₁ c₂ : QCircuit n)
    (h : c₁ ≅ c₂) : c₁ ⊨ .implementsMatrix c₂.denote := h

/-- A circuit satisfies equivalentTo(c') iff it's equivalent to c'. -/
theorem satisfies_equiv_iff {n : ℕ} (c c' : QCircuit n) :
    (c ⊨ .equivalentTo c') ↔ c ≅ c' := Iff.rfl

-- ---------------------------------------------------------------------------
-- Gate count monotonicity
-- ---------------------------------------------------------------------------

/-- If a circuit satisfies a gate count bound k, it satisfies any bound ≥ k. -/
theorem satisfies_gateCount_mono {n : ℕ} (c : QCircuit n)
    (pred : Gate n → Bool) (k k' : ℕ) (hk : k ≤ k')
    (h : c ⊨ .gateCount pred k) : c ⊨ .gateCount pred k' :=
  Nat.le_trans h hk

-- ---------------------------------------------------------------------------
-- Single-gate circuits
-- ---------------------------------------------------------------------------

/-- A single-gate circuit has gate count exactly 1. -/
theorem ofGate_gateCount_self {n : ℕ} (g : Gate n) (pred : Gate n → Bool)
    (hpred : pred g = true) :
    (QCircuit.ofGate g) ⊨ .gateCount pred 1 := by
  simp [satisfies, ofGate, countGates, hpred]

/-- Empty circuit has gate count 0. -/
theorem empty_gateCount_zero {n : ℕ} (pred : Gate n → Bool) :
    (QCircuit.empty : QCircuit n) ⊨ .gateCount pred 0 := by
  simp [satisfies, countGates]

end LeanQVerify
