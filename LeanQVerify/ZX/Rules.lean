import LeanQVerify.ZX.Semantics

/-!
# ZX-Calculus Rewrite Rules

Equational theorems for `ZXDiagram.denote`, corresponding to the standard
axioms of the ZX-calculus (Coecke & Duncan 2008).

## Rules proved here

* `hadamard_inv`     — H ⊚ H = wire
* `zSpider_zero`     — Z(1,1,0) = wire
* `xSpider_zero`     — X(1,1,0) = wire
* `color_change`     — H ⊚ Z(1,1,α) ⊚ H = X(1,1,α)
* `zSpider_fusion`   — Z(m,k,α) ⊚ Z(k,n,β) = Z(m,n,α+β)  (m,k,n ≥ 1)
* `nWires_denote_id` — ⟦nWires n⟧ = 1

## Note on spider fusion

The `zSpider_fusion` rule requires `m, k, n ≥ 1`. When m = 0 or n = 0 the
all-zeros and all-ones bitstrings coincide (both are the empty string), so the
`zSpiderMat` definition returns 1 rather than `exp(Iα)` for the (0,0) entry,
breaking the decomposition. This is a standard limitation of the matrix
semantics for boundary-less spiders; they are handled by a separate scalar
factor in more complete ZX presentations.

## References

Coecke, Duncan. "Interacting quantum observables". ICALP 2008.
van de Wetering. "ZX-calculus for the working quantum computer scientist". 2020.
-/

namespace LeanQVerify.ZX

open ZXDiagram Complex Matrix BigOperators Kronecker

-- ============================================================
-- Computational basis vectors
-- ============================================================

/-- All-zeros computational basis ket for n qubits. -/
private noncomputable def e0 (n : ℕ) : Fin (2 ^ n) → ℂ :=
  fun i => if i.val = 0 then 1 else 0

/-- All-ones computational basis ket for n qubits. -/
private noncomputable def e1 (n : ℕ) : Fin (2 ^ n) → ℂ :=
  fun i => if i.val = 2 ^ n - 1 then 1 else 0

-- e0 · e0 = 1
private lemma e0_inner (n : ℕ) : dotProduct (e0 n) (e0 n) = 1 := by
  have key : (fun i : Fin (2^n) => e0 n i * e0 n i) = e0 n := by
    funext i; simp [e0]
  simp only [dotProduct, key]
  rw [Finset.sum_eq_single (⟨0, Nat.two_pow_pos n⟩ : Fin (2^n))]
  · simp [e0]
  · intro i _ hi; simp [e0, show i.val ≠ 0 from fun h => hi (Fin.ext h)]
  · simp

-- e1 · e1 = 1
private lemma e1_inner (n : ℕ) : dotProduct (e1 n) (e1 n) = 1 := by
  have key : (fun i : Fin (2^n) => e1 n i * e1 n i) = e1 n := by
    funext i; simp [e1]
  simp only [dotProduct, key]
  rw [Finset.sum_eq_single (⟨2^n - 1, Nat.sub_lt (Nat.two_pow_pos n) one_pos⟩ : Fin (2^n))]
  · simp [e1]
  · intro i _ hi; simp [e1, show i.val ≠ 2^n - 1 from fun h => hi (Fin.ext h)]
  · simp

-- e0 · e1 = 0  (requires n ≥ 1 so all-zeros ≠ all-ones)
private lemma e0_e1_ortho (n : ℕ) (hn : 0 < n) : dotProduct (e0 n) (e1 n) = 0 := by
  have hne : (0 : ℕ) ≠ 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  simp only [dotProduct, e0, e1]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi0 : i.val = 0
  · rw [hi0, if_pos rfl, if_neg hne, mul_zero]
  · simp [hi0]

-- ============================================================
-- zSpiderMat as two rank-1 outer products
-- (valid when m, n ≥ 1 so |0...0⟩ ≠ |1...1⟩)
-- ============================================================

private lemma zSpiderMat_decomp (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (α : ℝ) :
    zSpiderMat m n α =
    Matrix.of (fun i j => e0 n i * e0 m j) +
    exp (I * ↑α) • Matrix.of (fun i j => e1 n i * e1 m j) := by
  have hm_ne : (0 : ℕ) ≠ 2 ^ m - 1 := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm; omega
  have hn_ne : (0 : ℕ) ≠ 2 ^ n - 1 := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn; omega
  ext out inp
  simp only [zSpiderMat, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
             e0, e1, smul_eq_mul]
  by_cases hi0 : inp.val = 0 <;>
  by_cases ho0 : out.val = 0 <;>
  by_cases hi1 : inp.val = 2 ^ m - 1 <;>
  by_cases ho1 : out.val = 2 ^ n - 1 <;>
  simp_all

-- ============================================================
-- Outer-product multiplication: (u v^T)(w x^T) = ⟨v,w⟩ · u x^T
-- ============================================================

private lemma outer_mul_outer {m k n : ℕ}
    (u : Fin (2 ^ n) → ℂ) (v : Fin (2 ^ k) → ℂ)
    (w : Fin (2 ^ k) → ℂ) (x : Fin (2 ^ m) → ℂ) :
    Matrix.of (fun i j => u i * v j) * Matrix.of (fun i j => w i * x j) =
    dotProduct v w • Matrix.of (fun i j => u i * x j) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, dotProduct, smul_eq_mul]
  simp_rw [show ∀ mid : Fin (2 ^ k), (u i * v mid) * (w mid * x j) =
      u i * x j * (v mid * w mid) from fun mid => by ring]
  rw [← Finset.mul_sum]
  ring

-- ============================================================
-- Spider fusion: Z(m,k,α) ∘ Z(k,n,β) = Z(m,n,α+β)
-- ============================================================

lemma zSpiderMat_mul (m k n : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (α β : ℝ) : zSpiderMat k n β * zSpiderMat m k α = zSpiderMat m n (α + β) := by
  rw [zSpiderMat_decomp m k hm hk α, zSpiderMat_decomp k n hk hn β]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  simp only [outer_mul_outer (e0 n) (e0 k) (e0 k) (e0 m),
             outer_mul_outer (e0 n) (e0 k) (e1 k) (e1 m),
             outer_mul_outer (e1 n) (e1 k) (e0 k) (e0 m),
             outer_mul_outer (e1 n) (e1 k) (e1 k) (e1 m)]
  have he10 : dotProduct (e1 k) (e0 k) = 0 := by
    rw [dotProduct_comm]; exact e0_e1_ortho k hk
  rw [e0_inner k, e1_inner k, e0_e1_ortho k hk, he10]
  simp only [zero_smul, smul_zero, add_zero, zero_add, one_smul, smul_smul]
  rw [show exp (I * ↑α) * exp (I * ↑β) = exp (I * ↑(α + β)) from by
    rw [← Complex.exp_add]; congr 1; rw [Complex.ofReal_add]; ring]
  exact (zSpiderMat_decomp m n hm hn (α + β)).symm

-- ============================================================
-- Helper: hadN 1 = H_mat
-- ============================================================

lemma hadN_one : hadN 1 = H_mat := by
  ext i j
  simp only [hadN, tensorMat, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  have hsymm : ∀ x : Fin 2, (finTwoPow_equiv 0 1).symm x = (⟨0, one_pos⟩, x) := by
    intro x
    apply (finTwoPow_equiv 0 1).injective
    simp only [finTwoPow_equiv, Equiv.trans_apply, finProdFinEquiv, finCongr,
               Equiv.coe_fn_mk, Fin.val, Equiv.apply_symm_apply]
    simp [Fin.ext_iff]
  rw [hsymm i, hsymm j]
  simp [hadN, Matrix.one_apply]

-- ============================================================
-- Basic diagram laws
-- ============================================================

/-- H ∘ H = identity wire. -/
theorem hadamard_inv :
    ZX⟦(hadamard ⊚ hadamard : ZXDiagram 1 1)⟧ = ZX⟦wire⟧ := by
  simp [H_mat_unitary]

/-- Zero-phase Z-spider (1→1) is the identity wire. -/
theorem zSpider_zero :
    ZX⟦(zSpider 1 1 0 : ZXDiagram 1 1)⟧ = ZX⟦wire⟧ := by
  simp [zSpiderMat_11_zero]

/-- Zero-phase X-spider (1→1) is the identity wire. -/
theorem xSpider_zero :
    ZX⟦(xSpider 1 1 0 : ZXDiagram 1 1)⟧ = ZX⟦wire⟧ := by
  simp only [denote_xSpider, denote_wire, xSpiderMat, hadN_one, zSpiderMat_11_zero]
  simp [H_mat_unitary]

-- ============================================================
-- Color change: Z ↔ X under Hadamard conjugation
-- ============================================================

/-- **Color change**: `H ∘ Z(α) ∘ H = X(α)`. -/
theorem color_change (α : ℝ) :
    ZX⟦(hadamard ⊚ zSpider 1 1 α) ⊚ hadamard⟧ = ZX⟦xSpider 1 1 α⟧ := by
  simp only [denote_compose, denote_hadamard, denote_zSpider, denote_xSpider,
             xSpiderMat, hadN_one]
  exact (mul_assoc H_mat (zSpiderMat 1 1 α) H_mat).symm

-- ============================================================
-- Spider fusion
-- ============================================================

/-- **Z-spider fusion**: two connected Z-spiders fuse with phase addition.
    Requires m, k, n ≥ 1. -/
theorem zSpider_fusion (m k n : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (α β : ℝ) :
    ZX⟦zSpider m k α ⊚ zSpider k n β⟧ = ZX⟦zSpider m n (α + β)⟧ := by
  simp [zSpiderMat_mul m k n hm hk hn α β]

-- ============================================================
-- n parallel identity wires denote the identity matrix
-- ============================================================

lemma tensorMat_one_one (n : ℕ) :
    tensorMat (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
              (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) = 1 := by
  ext i j
  simp only [tensorMat, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
             mul_ite, ite_mul, one_mul, mul_one, zero_mul, mul_zero]
  by_cases h : i = j
  · subst h; simp
  · simp only [if_neg h]
    have hne : (finTwoPow_equiv n 1).symm i ≠ (finTwoPow_equiv n 1).symm j :=
      fun heq => h ((finTwoPow_equiv n 1).symm.injective heq)
    by_cases h1 : ((finTwoPow_equiv n 1).symm i).1 = ((finTwoPow_equiv n 1).symm j).1
    · simp only [if_pos h1]
      have h2 : ¬((finTwoPow_equiv n 1).symm i).2 = ((finTwoPow_equiv n 1).symm j).2 :=
        fun heq2 => hne (by simp only [Prod.ext_iff]; exact ⟨h1, heq2⟩)
      simp [if_neg h2]
    · simp [if_neg h1]

/-- n parallel wires denote the identity matrix. -/
theorem nWires_denote_id (n : ℕ) : ZX⟦nWires n⟧ = 1 := by
  induction n with
  | zero =>
    ext i j
    fin_cases i; fin_cases j
    simp [nWires, denote_zSpider, zSpiderMat, Matrix.one_apply]
  | succ n ih =>
    simp only [nWires, denote_tensor, denote_wire, ih]
    exact tensorMat_one_one n

end LeanQVerify.ZX
