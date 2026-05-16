import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantum States

An n-qubit pure quantum state is a unit vector in ℂ^(2^n).
Qubit ordering: qubit 0 is the least-significant bit of the basis index.
So |q_{n-1} … q_1 q_0⟩ corresponds to index q_0 + 2·q_1 + … + 2^{n-1}·q_{n-1}.
-/

namespace LeanQVerify

open BigOperators Complex

/-- An n-qubit pure quantum state: a unit vector in ℂ^(2^n). -/
structure QState (n : ℕ) where
  val  : Fin (2 ^ n) → ℂ
  norm : ∑ i, normSq (val i) = 1

namespace QState

/-- The probability of measuring outcome k. -/
def prob {n : ℕ} (ψ : QState n) (k : Fin (2 ^ n)) : ℝ :=
  normSq (ψ.val k)

/-- Probabilities are non-negative. -/
theorem prob_nonneg {n : ℕ} (ψ : QState n) (k : Fin (2 ^ n)) : 0 ≤ ψ.prob k :=
  normSq_nonneg _

/-- Probabilities sum to 1. -/
theorem prob_sum_one {n : ℕ} (ψ : QState n) : ∑ k, ψ.prob k = 1 :=
  ψ.norm

-- ---------------------------------------------------------------------------
-- Standard single-qubit basis states
-- ---------------------------------------------------------------------------

/-- |0⟩ — the ground state. -/
def ket0 : QState 1 :=
  ⟨![1, 0], by simp [Fin.sum_univ_two, normSq_one]⟩

/-- |1⟩ — the excited state. -/
def ket1 : QState 1 :=
  ⟨![0, 1], by simp [Fin.sum_univ_two, normSq_one]⟩

/-- |+⟩ = (|0⟩ + |1⟩) / √2 — equal superposition with positive phase. -/
noncomputable def ketPlus : QState 1 :=
  ⟨fun _ => (Real.sqrt 2 : ℂ)⁻¹, by
    simp [Fin.sum_univ_two, normSq_inv, normSq_ofReal,
          Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)]⟩

/-- |−⟩ = (|0⟩ − |1⟩) / √2 — equal superposition with negative phase. -/
noncomputable def ketMinus : QState 1 :=
  ⟨![((Real.sqrt 2 : ℂ))⁻¹, -((Real.sqrt 2 : ℂ))⁻¹], by
    simp [Fin.sum_univ_two, normSq_neg, normSq_inv, normSq_ofReal,
          Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    norm_num⟩

-- ---------------------------------------------------------------------------
-- Two-qubit basis states
-- ---------------------------------------------------------------------------

/-- |00⟩ -/
def ket00 : QState 2 :=
  ⟨![1, 0, 0, 0], by simp [Fin.sum_univ_four, normSq_one]⟩

/-- |01⟩ -/
def ket01 : QState 2 :=
  ⟨![0, 1, 0, 0], by simp [Fin.sum_univ_four, normSq_one]⟩

/-- |10⟩ -/
def ket10 : QState 2 :=
  ⟨![0, 0, 1, 0], by simp [Fin.sum_univ_four, normSq_one]⟩

/-- |11⟩ -/
def ket11 : QState 2 :=
  ⟨![0, 0, 0, 1], by simp [Fin.sum_univ_four, normSq_one]⟩

/-- The Bell state |Φ+⟩ = (|00⟩ + |11⟩) / √2. -/
noncomputable def bellPhi : QState 2 :=
  ⟨![((Real.sqrt 2 : ℂ))⁻¹, 0, 0, ((Real.sqrt 2 : ℂ))⁻¹], by
    simp [Fin.sum_univ_four, normSq_inv, normSq_ofReal,
          Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    norm_num⟩

end QState
end LeanQVerify
