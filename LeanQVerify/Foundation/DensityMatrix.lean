import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import LeanQVerify.Foundation.QState

/-!
# Density Matrices

A density matrix ρ satisfies: ρ† = ρ, ρ ≥ 0, tr(ρ) = 1.
-/

namespace LeanQVerify

open Matrix Complex BigOperators

private def matPosSemidef {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  M.IsHermitian ∧ ∀ x : Fin k → ℂ, 0 ≤ (dotProduct (star x) (M.mulVec x)).re

structure DensityMatrix (n : ℕ) where
  mat       : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  hermitian : mat.conjTranspose = mat
  pos_sdef  : matPosSemidef mat
  trace_one : mat.trace = 1

namespace DensityMatrix

-- Helper: (starRingEnd ℂ) applied twice is identity and distributes over mul.
-- Used for: star(a * conj b) = conj(a) * b  (ℂ commutative so = b * conj a).
private lemma conjSwap (a b : ℂ) :
    star (a * starRingEnd ℂ b) = b * starRingEnd ℂ a := by
  rw [← starRingEnd_apply, map_mul (starRingEnd ℂ), starRingEnd_self_apply, starRingEnd_apply]
  ring

noncomputable def ofPure {n : ℕ} (ψ : QState n) : DensityMatrix n where
  mat := Matrix.of fun i j => ψ.val i * starRingEnd ℂ (ψ.val j)
  hermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact conjSwap (ψ.val j) (ψ.val i)
  pos_sdef := by
    refine ⟨?_, ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
      exact conjSwap (ψ.val j) (ψ.val i)
    · intro v
      let c : ℂ := ∑ j : Fin (2 ^ n), star (ψ.val j) * v j
      -- (ρ v)_k = ψ_k * c
      have hmv : ∀ k : Fin (2 ^ n),
          (Matrix.of (fun i j => ψ.val i * starRingEnd ℂ (ψ.val j))).mulVec v k
          = ψ.val k * c := by
        intro k
        simp only [Matrix.mulVec, Matrix.of_apply, starRingEnd_apply, c]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      -- ∑_k star(v_k) * ψ_k = star c
      have hsc : ∑ k : Fin (2 ^ n), star (v k) * ψ.val k = star c := by
        show ∑ k : Fin (2 ^ n), star (v k) * ψ.val k =
             star (∑ j : Fin (2 ^ n), star (ψ.val j) * v j)
        rw [star_sum]
        apply Finset.sum_congr rfl; intro k _
        -- star(star(ψ_k) * v_k) = conj(conj(ψ_k)) * conj(v_k) = ψ_k * star(v_k)
        -- and LHS = star(v_k) * ψ_k  so both = ψ_k * star(v_k) by mul_comm
        conv_rhs =>
          rw [← starRingEnd_apply, map_mul (starRingEnd ℂ), ← starRingEnd_apply,
              starRingEnd_self_apply, starRingEnd_apply]
        ring
      -- v† ρ v = normSq c ≥ 0
      suffices h : (dotProduct (star v)
              ((Matrix.of (fun i j => ψ.val i * starRingEnd ℂ (ψ.val j))).mulVec v)).re
            = Complex.normSq c by rw [h]; exact Complex.normSq_nonneg c
      simp_rw [dotProduct, hmv, Pi.star_apply]
      have hsum : ∑ k : Fin (2 ^ n), star (v k) * (ψ.val k * c) = star c * c := by
        simp_rw [← mul_assoc]; rw [← Finset.sum_mul, hsc]
      rw [hsum]
      -- (star c * c).re = normSq c
      have hre : (star c * c).re = Complex.normSq c := by
        rw [show star c = (starRingEnd ℂ) c from (starRingEnd_apply c).symm,
            ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      rw [hre]
  trace_one := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    have h : ∀ i : Fin (2 ^ n),
        ψ.val i * starRingEnd ℂ (ψ.val i) = ↑(Complex.normSq (ψ.val i)) :=
      fun i => Complex.mul_conj (ψ.val i)
    simp_rw [h, ← Complex.ofReal_sum, ψ.norm, Complex.ofReal_one]

noncomputable def applyUnitary {n : ℕ}
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U.conjTranspose * U = 1)
    (ρ : DensityMatrix n) : DensityMatrix n where
  mat := U * ρ.mat * U.conjTranspose
  hermitian := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, ρ.hermitian, mul_assoc]
  pos_sdef := by
    refine ⟨?_, ?_⟩
    · show (U * ρ.mat * U.conjTranspose).conjTranspose = U * ρ.mat * U.conjTranspose
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, ρ.hermitian, mul_assoc]
    · intro v
      have h := ρ.pos_sdef.2 (U.conjTranspose.mulVec v)
      suffices heq :
          (dotProduct (star v) ((U * ρ.mat * U.conjTranspose).mulVec v)).re =
          (dotProduct (star (U.conjTranspose.mulVec v))
            (ρ.mat.mulVec (U.conjTranspose.mulVec v))).re by
        rw [heq]; exact h
      congr 1
      have hfold : (U * ρ.mat * U.conjTranspose).mulVec v =
                   U.mulVec (ρ.mat.mulVec (U.conjTranspose.mulVec v)) := by
        rw [mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      -- U.vecMul(star v) k = star(U†v) k, i.e., ∑_i star(v_i)*U_ik = star(∑_i star(U_ik)*v_i)
      have hvec : U.vecMul (star v) = star (U.conjTranspose.mulVec v) := by
        funext k
        -- Expand both sides definitionally
        show ∑ i, (star v) i * U i k =
             star (∑ i : Fin (2 ^ n), U.conjTranspose k i * v i)
        simp only [Pi.star_apply, Matrix.conjTranspose_apply]
        rw [star_sum]
        apply Finset.sum_congr rfl; intro i _
        conv_rhs =>
          rw [← starRingEnd_apply, map_mul (starRingEnd ℂ), ← starRingEnd_apply,
              starRingEnd_self_apply, starRingEnd_apply]
        ring
      rw [hfold, dotProduct_mulVec, hvec]
  trace_one := by
    rw [Matrix.trace_mul_comm (U * ρ.mat) U.conjTranspose, ← mul_assoc, hU, one_mul]
    exact ρ.trace_one

noncomputable def measure {n : ℕ} (i : Fin n) (ρ : DensityMatrix n) :
    ℝ × ℝ × DensityMatrix n × DensityMatrix n :=
  -- Projector onto computational-basis states where qubit i has value b
  let proj (b : Bool) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    Matrix.diagonal fun k => if k.val.testBit i.val = b then 1 else 0
  -- Born-rule probabilities: p_b = Tr(Π_b ρ)
  let p₀ : ℝ := ((proj false) * ρ.mat).trace.re
  let p₁ : ℝ := ((proj true)  * ρ.mat).trace.re
  -- Post-measurement state collapse (Π_b ρ Π_b / p_b) is deferred;
  -- ρ is returned as a valid placeholder. See DensityMatrix.ofPure / applyUnitary
  -- for the collapse model — classical communication is out of scope for this version.
  (p₀, p₁, ρ, ρ)

end DensityMatrix
end LeanQVerify
