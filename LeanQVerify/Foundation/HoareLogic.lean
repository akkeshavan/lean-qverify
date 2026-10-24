import LeanQVerify.Foundation.DensityMatrix
import LeanQVerify.Circuit.QCircuit
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Quantum Hoare Logic (Phase 1 — native)

Defines quantum predicates and a denotational Hoare triple
`HoareTriple A c B` with the standard proof rules.

## Semantics

A *quantum predicate* `QPred n` is a `2ⁿ×2ⁿ` Hermitian matrix A with
`0 ≤ A ≤ I` in the Löwner order.  The triple `{A} c {B}` means

    ∀ ρ (density), tr(A·ρ) ≤ tr(B · (c(ρ)))

where `c(ρ) = c.denote · ρ · c.denote†`.

## Rules

* `hoare_skip`       — `{A} skip {A}`
* `hoare_gate`       — `{U†AU} gate(g) {A}`  (U = g.matrix, requires `U†U = 1`)
* `hoare_seq`        — composition (requires c₁ unitary)
* `hoare_consequence` — pre/post weakening
-/

namespace LeanQVerify
open Matrix Complex BigOperators QCircuit

-- ============================================================
-- PSD predicate (internal)
-- ============================================================

private def matPSD {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  M.IsHermitian ∧ ∀ x : Fin k → ℂ, 0 ≤ (dotProduct (star x) (M.mulVec x)).re

private lemma single_dotProduct_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (i : Fin k) :
    dotProduct (star (Pi.single i (1:ℂ))) (M.mulVec (Pi.single i 1)) = M i i := by
  simp [dotProduct, mulVec, Pi.single_apply, apply_ite (star : ℂ → ℂ),
        Finset.sum_ite_eq', Finset.mem_univ]

private lemma matPSD_diag_nonneg {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ}
    (h : matPSD M) (i : Fin k) : 0 ≤ (M i i).re :=
  single_dotProduct_mulVec M i ▸ h.2 (Pi.single i 1)

private lemma matPSD_trace_nonneg {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ}
    (h : matPSD M) : 0 ≤ M.trace.re := by
  simp only [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => matPSD_diag_nonneg h i

-- ============================================================
-- PSD congruence helpers
-- ============================================================

private lemma dotProduct_mulVec_adjoint {k : ℕ} (U : Matrix (Fin k) (Fin k) ℂ)
    (x v : Fin k → ℂ) :
    dotProduct (star x) (U.mulVec v) = dotProduct (star (U.conjTranspose.mulVec x)) v := by
  simp only [dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply]
  simp_rw [star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext i; congr 1; ext j; ring

private lemma trace_diagonal_mul {k : ℕ} (f : Fin k → ℂ) (M : Matrix (Fin k) (Fin k) ℂ) :
    (diagonal f * M).trace = ∑ i, f i * M i i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

-- Congruence: U·ρ·U† is PSD whenever ρ is PSD.
private lemma matPSD_conj {k : ℕ} (U : Matrix (Fin k) (Fin k) ℂ)
    {ρ : Matrix (Fin k) (Fin k) ℂ} (hρ : matPSD ρ) : matPSD (U * ρ * U.conjTranspose) := by
  constructor
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hρ.1, mul_assoc]
  · intro x
    rw [show U * ρ * U.conjTranspose = U * (ρ * U.conjTranspose) from mul_assoc _ _ _,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec_adjoint]
    exact hρ.2 _

-- ============================================================
-- Trace lemmas
-- ============================================================

private lemma trace_conj_cycle {k : ℕ} (A U ρ : Matrix (Fin k) (Fin k) ℂ) :
    (A * (U * ρ * U.conjTranspose)).trace = (U.conjTranspose * A * U * ρ).trace := by
  rw [show A * (U * ρ * U.conjTranspose) = A * U * ρ * U.conjTranspose by simp [mul_assoc]]
  rw [Matrix.trace_mul_comm (A * U * ρ) U.conjTranspose]; simp [mul_assoc]

-- Hilbert-Schmidt self-duality: tr(AB) ≥ 0 for PSD A, B.
-- Proof: spectral decompose A = S D S†, cycle trace to get Σᵢ λᵢ (S†BS)ᵢᵢ ≥ 0.
private lemma trace_psd_mul_nonneg {k : ℕ} {C ρ : Matrix (Fin k) (Fin k) ℂ}
    (hC : matPSD C) (hρ : matPSD ρ) : 0 ≤ ((C * ρ).trace).re := by
  classical
  have hIsHerm : Matrix.IsHermitian C := hC.1
  let eigs : Fin k → ℝ := hIsHerm.eigenvalues
  let S : Matrix (Fin k) (Fin k) ℂ := (hIsHerm.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
  have hSS : star S * S = 1 := Matrix.mem_unitaryGroup_iff'.mp hIsHerm.eigenvectorUnitary.2
  have hSS2 : S * star S = 1 := Matrix.mem_unitaryGroup_iff.mp hIsHerm.eigenvectorUnitary.2
  have hSCS : star S * C * S = diagonal (RCLike.ofReal ∘ eigs) := by
    have h := hIsHerm.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_star_apply] at h; exact h
  have hspec : C = S * diagonal (RCLike.ofReal ∘ eigs) * star S :=
    calc C = 1 * C * 1 := by simp only [one_mul, mul_one]
      _ = (S * star S) * C * (S * star S) := by simp only [← hSS2]
      _ = S * (star S * C * S) * star S := by simp only [mul_assoc]
      _ = S * diagonal (RCLike.ofReal ∘ eigs) * star S := by rw [hSCS]
  have hdiag : matPSD (diagonal (RCLike.ofReal ∘ eigs)) := by
    have h := matPSD_conj (star S) hC
    have heq : star S * C * (star S).conjTranspose = star S * C * S := by
      congr 1; ext i j; simp [Matrix.conjTranspose_apply]
    rw [heq] at h; rwa [hSCS] at h
  rw [hspec]
  have hcyc : (S * diagonal (RCLike.ofReal ∘ eigs) * star S * ρ).trace =
              (diagonal (RCLike.ofReal ∘ eigs) * (star S * ρ * S)).trace := by
    have h1 : S * diagonal (RCLike.ofReal ∘ eigs) * star S * ρ =
              S * diagonal (RCLike.ofReal ∘ eigs) * (star S * ρ) := by simp only [mul_assoc]
    have h2 : (star S * ρ) * (S * diagonal (RCLike.ofReal ∘ eigs)) =
              (star S * ρ * S) * diagonal (RCLike.ofReal ∘ eigs) := by simp only [mul_assoc]
    rw [h1, Matrix.trace_mul_comm (S * diagonal _) (star S * ρ), h2,
        Matrix.trace_mul_comm (star S * ρ * S) (diagonal _)]
  rw [hcyc, trace_diagonal_mul, Complex.re_sum]
  apply Finset.sum_nonneg; intro i _
  simp only [Function.comp]
  have hmul : (RCLike.ofReal (eigs i) * (star S * ρ * S) i i).re =
              eigs i * ((star S * ρ * S) i i).re := by
    simp only [coe_algebraMap, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [hmul]; apply mul_nonneg
  · have h := matPSD_diag_nonneg hdiag i
    simp only [Matrix.diagonal_apply_eq, Function.comp, coe_algebraMap, ofReal_re] at h
    exact_mod_cast h
  · have h := matPSD_conj (star S) hρ
    have heq : star S * ρ * (star S).conjTranspose = star S * ρ * S := by
      congr 1; ext i j; simp [Matrix.conjTranspose_apply]
    rw [heq] at h; exact matPSD_diag_nonneg h i

private lemma trace_psd_mono {k : ℕ} {A B ρ : Matrix (Fin k) (Fin k) ℂ}
    (hAB : matPSD (B - A)) (hρ : matPSD ρ) :
    ((A * ρ).trace).re ≤ ((B * ρ).trace).re := by
  have : (((B - A) * ρ).trace).re = ((B * ρ).trace).re - ((A * ρ).trace).re := by
    rw [show (B - A) * ρ = B * ρ - A * ρ by simp [sub_mul], Matrix.trace_sub, Complex.sub_re]
  linarith [trace_psd_mul_nonneg hAB hρ]

-- Cyclic trace: tr(U·ρ·U†) = tr(ρ) when U†U = 1.
private lemma trace_conj_eq {k : ℕ} (U ρ : Matrix (Fin k) (Fin k) ℂ)
    (hU : U.conjTranspose * U = 1) : (U * ρ * U.conjTranspose).trace = ρ.trace := by
  rw [Matrix.trace_mul_comm (U * ρ) U.conjTranspose, ← mul_assoc, hU, one_mul]

-- ============================================================
-- Quantum predicates and Hoare triple
-- ============================================================

/-- A quantum predicate: a `2ⁿ×2ⁿ` Hermitian matrix A with `0 ≤ A ≤ I`. -/
structure QPred (n : ℕ) where
  mat : Matrix (Fin (2^n)) (Fin (2^n)) ℂ
  pos : matPSD mat
  le1 : matPSD (1 - mat)

/-- The conjugate predicate `U†·A·U` (valid QPred when U is unitary, `hU : U†U = 1`). -/
noncomputable def QPred.conj {n : ℕ} (A : QPred n)
    (U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hU : U.conjTranspose * U = 1) : QPred n where
  mat := U.conjTranspose * A.mat * U
  pos := by
    have h := matPSD_conj U.conjTranspose A.pos
    rwa [Matrix.conjTranspose_conjTranspose] at h
  le1 := by
    have h := matPSD_conj U.conjTranspose A.le1
    rw [Matrix.conjTranspose_conjTranspose] at h
    convert h using 2
    rw [mul_sub, mul_one, sub_mul, hU]

/-- The zero predicate. tr(0·ρ) = 0 for all ρ. -/
noncomputable def QPred.trivial (n : ℕ) : QPred n where
  mat := 0
  pos := ⟨by simp [Matrix.IsHermitian],
          fun x => by simp [dotProduct, Matrix.zero_mulVec]⟩
  le1 := ⟨by simp [Matrix.IsHermitian, sub_zero],
          fun x => by
            simp only [sub_zero, Matrix.one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]
            apply Finset.sum_nonneg; intro i _
            have heq : (star (x i) * x i).re = (x i).re ^ 2 + (x i).im ^ 2 := by
              simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
              ring
            linarith [sq_nonneg (x i).re, sq_nonneg (x i).im, heq]⟩

/-- The identity predicate. tr(I·ρ) = tr(ρ) = 1 for all unit-trace ρ. -/
noncomputable def QPred.full (n : ℕ) : QPred n where
  mat := 1
  pos := ⟨by simp [Matrix.IsHermitian],
          fun x => by
            rw [Matrix.one_mulVec]
            simp only [dotProduct, Pi.star_apply, Complex.re_sum]
            apply Finset.sum_nonneg; intro i _
            have heq : (star (x i) * x i).re = (x i).re ^ 2 + (x i).im ^ 2 := by
              simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
              ring
            linarith [sq_nonneg (x i).re, sq_nonneg (x i).im, heq]⟩
  le1 := ⟨by simp [Matrix.IsHermitian, sub_self],
          fun x => by simp [sub_self, dotProduct, Matrix.zero_mulVec]⟩

/-- Apply circuit c to density operator ρ: `c.denote · ρ · c.denote†`. -/
noncomputable def QCircuit.applyDO {n : ℕ} (c : QCircuit n)
    (ρ : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :=
  c.denote * ρ * c.denote.conjTranspose

/-- Quantum Hoare triple `{A} c {B}`:
    for all density operators ρ, `tr(A·ρ) ≤ tr(B · c(ρ))`. -/
def HoareTriple {n : ℕ} (A : QPred n) (c : QCircuit n) (B : QPred n) : Prop :=
  ∀ ρ : Matrix (Fin (2^n)) (Fin (2^n)) ℂ,
    matPSD ρ → ρ.trace = 1 →
    ((A.mat * ρ).trace).re ≤ ((B.mat * c.applyDO ρ).trace).re

-- ============================================================
-- Proof rules
-- ============================================================

/-- Skip rule: `{A} skip {A}`. -/
theorem hoare_skip {n : ℕ} (A : QPred n) :
    HoareTriple A (QCircuit.empty (n := n)) A := fun ρ _ _ => by
  simp [QCircuit.applyDO, denote_empty]

/-- Gate rule: `{U†AU} gate(g) {A}` where `U = g.matrix`, `hU : U†U = 1`. -/
theorem hoare_gate {n : ℕ} (A : QPred n) (g : Gate n)
    (hU : g.matrix.conjTranspose * g.matrix = 1) :
    HoareTriple (A.conj g.matrix hU) (ofGate g) A := by
  intro ρ _ _
  simp only [QCircuit.applyDO, ofGate, denote_cons, denote_empty, one_mul, QPred.conj]
  exact le_of_eq (congr_arg Complex.re (trace_conj_cycle A.mat g.matrix ρ).symm)

/-- Sequential rule: `{A} c₁ {B} → {B} c₂ {C} → {A} c₁;c₂ {C}`.
    Requires `c₁` to be unitary (`c₁.denote† · c₁.denote = 1`). -/
theorem hoare_seq {n : ℕ} {A B C : QPred n} {c₁ c₂ : QCircuit n}
    (hU₁ : c₁.denote.conjTranspose * c₁.denote = 1)
    (h₁ : HoareTriple A c₁ B) (h₂ : HoareTriple B c₂ C) :
    HoareTriple A (c₁ ++ c₂) C := by
  intro ρ hρ htr
  have hρ₁ : matPSD (c₁.applyDO ρ) := matPSD_conj c₁.denote hρ
  have htr₁ : (c₁.applyDO ρ).trace = 1 := by
    simp only [QCircuit.applyDO]; rw [trace_conj_eq c₁.denote ρ hU₁, htr]
  calc ((A.mat * ρ).trace).re
      ≤ ((B.mat * c₁.applyDO ρ).trace).re              := h₁ ρ hρ htr
    _ ≤ ((C.mat * c₂.applyDO (c₁.applyDO ρ)).trace).re := h₂ _ hρ₁ htr₁
    _ = ((C.mat * (c₁ ++ c₂).applyDO ρ).trace).re      := by
          simp only [QCircuit.applyDO, denote_seq, Matrix.conjTranspose_mul]
          congr 1; congr 1; simp [mul_assoc]

/-- Consequence rule: `A' ≤ A`, `{A} c {B}`, `B ≤ B'` → `{A'} c {B'}`. -/
theorem hoare_consequence {n : ℕ} {A A' B B' : QPred n} {c : QCircuit n}
    (hA : matPSD (A.mat - A'.mat)) (h : HoareTriple A c B) (hB : matPSD (B'.mat - B.mat)) :
    HoareTriple A' c B' := fun ρ hρ htr =>
  calc ((A'.mat * ρ).trace).re
      ≤ ((A.mat * ρ).trace).re               := trace_psd_mono hA hρ
    _ ≤ ((B.mat * c.applyDO ρ).trace).re     := h ρ hρ htr
    _ ≤ ((B'.mat * c.applyDO ρ).trace).re    := trace_psd_mono hB (matPSD_conj c.denote hρ)

end LeanQVerify
