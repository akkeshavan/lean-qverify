import LeanQVerify.ZX.Rules
import LeanQVerify.Foundation.Unitary

/-!
# Circuit-to-ZX Translation (Phase 3)

Proves that standard quantum gates have correct ZX-calculus matrix representations,
and establishes foundational lemmas needed for X-spider fusion.

## Main results

* `tensorMat_mul` — Kronecker product is compatible with matrix multiplication.
* `hadN_unitary` — The n-fold Hadamard tensor is self-inverse: `hadN k * hadN k = 1`.
* `zSpiderMat_11_half_pi` — Z-spider(1,1,π/2) = S gate.
* `zSpiderMat_11_quarter_pi` — Z-spider(1,1,π/4) = T gate.
* `xSpider_pi_eq_X` — X-spider(1,1,π) = X gate.
* `xSpider_fusion` — X-spider fusion (proved using `hadN_unitary`).
* `pi_copy` — π-copy rule: Z(π) commutes through an X-copy by duplicating onto both outputs.
-/

namespace LeanQVerify.ZX
open ZXDiagram Complex Matrix Real BigOperators Kronecker

-- ============================================================
-- Kronecker/tensor product multiplication
-- ============================================================

/-- tensorMat is compatible with matrix multiplication:
    `tensorMat A C * tensorMat B D = tensorMat (A * B) (C * D)`. -/
lemma tensorMat_mul {n₁ m₁ k₁ n₂ m₂ k₂ : ℕ}
    (A : Matrix (Fin (2 ^ n₁)) (Fin (2 ^ m₁)) ℂ)
    (C : Matrix (Fin (2 ^ n₂)) (Fin (2 ^ m₂)) ℂ)
    (B : Matrix (Fin (2 ^ m₁)) (Fin (2 ^ k₁)) ℂ)
    (D : Matrix (Fin (2 ^ m₂)) (Fin (2 ^ k₂)) ℂ) :
    tensorMat A C * tensorMat B D = tensorMat (A * B) (C * D) := by
  simp only [tensorMat]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul A B C D]

-- ============================================================
-- hadN unitarity: hadN k * hadN k = 1
-- ============================================================

/-- The n-fold Hadamard tensor is unitary: `hadN k * hadN k = 1`. -/
theorem hadN_unitary (k : ℕ) : hadN k * hadN k = 1 := by
  induction k with
  | zero => simp [hadN]
  | succ k ih =>
    simp only [hadN]
    rw [tensorMat_mul, ih, H_mat_unitary]
    exact tensorMat_one_one k

-- ============================================================
-- Z-spider phase-gate equivalences
-- ============================================================

/-- Z-spider(1,1,π/2) = S gate: `zSpiderMat 1 1 (π/2) = S_mat`. -/
theorem zSpiderMat_11_half_pi : zSpiderMat 1 1 (Real.pi / 2) = S_mat := by
  -- After simp [zSpiderMat], ofReal_div fires and rewrites ↑(π/2) → ↑π/2 in the goal.
  -- So hexp must be stated in that simplified form to match.
  have hexp : Complex.exp (Complex.I * (↑Real.pi / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_pi_div_two_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSpiderMat, S_mat, hexp]

/-- Z-spider(1,1,π/4) = T gate: `zSpiderMat 1 1 (π/4) = T_mat`. -/
theorem zSpiderMat_11_quarter_pi : zSpiderMat 1 1 (Real.pi / 4) = T_mat := by
  -- After simp [zSpiderMat], ofReal_div fires: ↑(π/4) → ↑π/4, leaving goal
  -- cexp (I * (↑π / 4)) = cexp (I * ↑π / 4); the two differ by mul_div_assoc.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSpiderMat, T_mat] <;> (try (congr 1; ring))

-- ============================================================
-- ZX representations of 1-qubit gates
-- ============================================================

/-- The Z gate is a Z-spider with phase π. -/
theorem zGate_as_zSpider :
    ZX⟦(zSpider 1 1 Real.pi : ZXDiagram 1 1)⟧ = Z_mat :=
  zSpiderMat_11_pi

/-- The S gate is a Z-spider with phase π/2. -/
theorem sGate_as_zSpider :
    ZX⟦(zSpider 1 1 (Real.pi / 2) : ZXDiagram 1 1)⟧ = S_mat :=
  zSpiderMat_11_half_pi

/-- The T gate is a Z-spider with phase π/4. -/
theorem tGate_as_zSpider :
    ZX⟦(zSpider 1 1 (Real.pi / 4) : ZXDiagram 1 1)⟧ = T_mat :=
  zSpiderMat_11_quarter_pi

private lemma sqrt2_sq_C' : ((Real.sqrt 2 : ℝ) : ℂ) * Real.sqrt 2 = 2 :=
  by exact_mod_cast Real.mul_self_sqrt (by norm_num)

private lemma H_Z_H_mat' : H_mat * (Z_mat * H_mat) = X_mat := by
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, sqrt2_sq_C']
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [H_mat, X_mat, Z_mat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (rw [hinv]; norm_num)

/-- The X gate is an X-spider with phase π. -/
theorem xSpider_pi_eq_X :
    ZX⟦(xSpider 1 1 Real.pi : ZXDiagram 1 1)⟧ = X_mat := by
  simp only [denote_xSpider, xSpiderMat, hadN_one, zSpiderMat_11_pi]
  rw [mul_assoc, H_Z_H_mat']

-- ============================================================
-- X-spider fusion (proved using hadN_unitary)
-- ============================================================

/-- **X-spider fusion**: two connected X-spiders fuse with phase addition.
    Requires m, k, n ≥ 1. -/
theorem xSpider_fusion (m k n : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (α β : ℝ) :
    ZX⟦xSpider m k α ⊚ xSpider k n β⟧ = ZX⟦xSpider m n (α + β)⟧ := by
  simp only [denote_compose, denote_xSpider, xSpiderMat]
  -- Goal: (hadN n * zSpiderMat k n β * hadN k) * (hadN k * zSpiderMat m k α * hadN m)
  --     = hadN n * zSpiderMat m n (α + β) * hadN m
  rw [Matrix.mul_assoc (hadN k) (zSpiderMat m k α) (hadN m),
      Matrix.mul_assoc (hadN n * zSpiderMat k n β) (hadN k)
        (hadN k * (zSpiderMat m k α * hadN m)),
      ← Matrix.mul_assoc (hadN k) (hadN k) (zSpiderMat m k α * hadN m),
      hadN_unitary k, Matrix.one_mul,
      ← Matrix.mul_assoc (hadN n * zSpiderMat k n β) (zSpiderMat m k α) (hadN m),
      Matrix.mul_assoc (hadN n) (zSpiderMat k n β) (zSpiderMat m k α),
      zSpiderMat_mul m k n hm hk hn α β]

-- ============================================================
-- CNOT ZX representation
-- ============================================================

/-- The standard ZX diagram for CNOT: Z-copy on control, X-merge on target. -/
noncomputable def cnotZX : ZXDiagram 2 2 :=
  (zSpider 1 2 0 ↑⊗ wire) ⊚ (wire ↑⊗ xSpider 2 1 0)

-- Sum expansion helpers for the Fin (2^k) syntactic forms produced by tensorMat
@[simp] private lemma sum_fin_2pow2 {M : Type*} [AddCommMonoid M] (f : Fin (2^2) → M) :
    ∑ x : Fin (2^2), f x = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

@[simp] private lemma sum_fin_2pow_2p1 {M : Type*} [AddCommMonoid M] (f : Fin (2^(2+1)) → M) :
    ∑ x : Fin (2^(2+1)), f x = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
  Fin.sum_univ_eight f

private lemma sqrt2_ne_zero_C_cnot : (↑(Real.sqrt 2) : ℂ) ≠ 0 :=
  by exact_mod_cast (Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)).ne'

private lemma sqrt2_sq_C_cnot : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
  rw [sq]; exact_mod_cast Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)

-- Explicit entry formula for xSpiderMat 2 1 0: nonzero only at (0,0),(0,3),(1,1),(1,2)
private lemma xSpider21_entry (p : Fin 2) (q : Fin 4) :
    xSpiderMat 2 1 0 p q =
    (↑(Real.sqrt 2) : ℂ)⁻¹ *
    if (p.val = 0 ∧ q.val = 0) ∨ (p.val = 0 ∧ q.val = 3) ∨
       (p.val = 1 ∧ q.val = 1) ∨ (p.val = 1 ∧ q.val = 2) then 1 else 0 := by
  simp only [xSpiderMat, hadN_one]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, sum_fin_2pow2]
  fin_cases p <;> fin_cases q <;>
  simp only [zSpiderMat, Matrix.of_apply, hadN, tensorMat,
             Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
             finTwoPow_equiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
             H_mat, Matrix.one_apply] <;>
  try norm_num
  all_goals (field_simp [sqrt2_ne_zero_C_cnot]; linear_combination -sqrt2_sq_C_cnot)

/-- The ZX CNOT diagram represents the 4×4 CNOT gate (up to the √2 normalisation
    from the ZX-calculus convention for X-spiders). Control = qubit 1, target = qubit 0. -/
theorem cnotZX_correct :
    (↑(Real.sqrt 2) : ℂ) • ZX⟦cnotZX⟧ = embedCNOT 2 ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ := by
  simp only [cnotZX, denote_compose, denote_tensor, denote_wire, denote_xSpider, denote_zSpider]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Matrix.smul_apply, Matrix.mul_apply, xSpider21_entry, sum_fin_2pow_2p1,
             tensorMat, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
             finTwoPow_equiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
             zSpiderMat, Matrix.of_apply, Matrix.one_apply, embedCNOT] <;>
  norm_num [sqrt2_ne_zero_C_cnot, sqrt2_sq_C_cnot, mul_inv_cancel₀] <;>
  decide

-- ============================================================
-- π-copy rule
-- ============================================================

-- Type aliases carrying Fin (2^1) so tensorMat can infer implicit nat args.
private noncomputable abbrev H1 : Matrix (Fin (2^1)) (Fin (2^1)) ℂ := H_mat
private abbrev X1 : Matrix (Fin (2^1)) (Fin (2^1)) ℂ := X_mat
private abbrev Z1 : Matrix (Fin (2^1)) (Fin (2^1)) ℂ := Z_mat

-- simp only uses syntactic matching: Fin (2^1) ≠ Fin 2, so dedicated sum lemmas are needed.
@[simp] private lemma sum_fin_2pow1 {M : Type*} [AddCommMonoid M] (f : Fin (2^1) → M) :
    ∑ x : Fin (2^1), f x = f 0 + f 1 := Fin.sum_univ_two f

@[simp] private lemma sum_fin_2pow_1p1 {M : Type*} [AddCommMonoid M] (f : Fin (2^(1+1)) → M) :
    ∑ x : Fin (2^(1+1)), f x = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

private lemma HZ_eq_XH : H_mat * Z_mat = X_mat * H_mat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H_mat, X_mat, Z_mat, Matrix.mul_apply, Fin.sum_univ_two]

private lemma HX_eq_ZH : H_mat * X_mat = Z_mat * H_mat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H_mat, X_mat, Z_mat, Matrix.mul_apply, Fin.sum_univ_two]

private lemma zSpiderMat_copy_X :
    zSpiderMat 1 2 0 * X_mat = tensorMat X1 X1 * zSpiderMat 1 2 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [Matrix.mul_apply, sum_fin_2pow1, sum_fin_2pow_1p1,
             tensorMat, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
             finTwoPow_equiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
             zSpiderMat, Matrix.of_apply,
             X_mat, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
  norm_num

private lemma hadN_two' : hadN 2 = tensorMat H1 H1 := by
  unfold hadN; rw [hadN_one]

/-- **π-copy rule**: a Z(π) node commutes through an X-copy by duplicating onto both outputs. -/
theorem pi_copy :
    ZX⟦(zSpider 1 1 Real.pi) ⊚ (xSpider 1 2 0)⟧
    = ZX⟦(xSpider 1 2 0) ⊚ ((zSpider 1 1 Real.pi) ↑⊗ (zSpider 1 1 Real.pi))⟧ := by
  simp only [denote_compose, denote_tensor, denote_zSpider, denote_xSpider, xSpiderMat,
             hadN_one, zSpiderMat_11_pi]
  rw [hadN_two']
  rw [Matrix.mul_assoc (tensorMat H1 H1 * zSpiderMat 1 2 0) H_mat Z_mat]
  rw [HZ_eq_XH]
  rw [← Matrix.mul_assoc (tensorMat H1 H1 * zSpiderMat 1 2 0) X_mat H_mat]
  rw [Matrix.mul_assoc (tensorMat H1 H1) (zSpiderMat 1 2 0) X_mat]
  rw [zSpiderMat_copy_X]
  rw [← Matrix.mul_assoc (tensorMat H1 H1) (tensorMat X1 X1) (zSpiderMat 1 2 0)]
  rw [tensorMat_mul H1 H1 X1 X1]
  rw [show H1 * X1 = Z1 * H1 from HX_eq_ZH]
  rw [← tensorMat_mul Z1 Z1 H1 H1]
  rw [Matrix.mul_assoc (tensorMat Z1 Z1 * tensorMat H1 H1) (zSpiderMat 1 2 0) H_mat]
  rw [Matrix.mul_assoc (tensorMat Z1 Z1) (tensorMat H1 H1) (zSpiderMat 1 2 0 * H_mat)]
  rw [Matrix.mul_assoc (tensorMat H1 H1) (zSpiderMat 1 2 0) H_mat]

end LeanQVerify.ZX
