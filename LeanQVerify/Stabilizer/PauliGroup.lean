import LeanQVerify.Foundation.Unitary
import LeanQVerify.Stabilizer.CliffordGate

/-!
# Pauli Group and Stabilizer Operators

Defines the single-qubit and n-qubit Pauli operators used by the
stabilizer tableau.  The convention follows Aaronson–Gottesman (2004):

  pauliMat x z = i^(x·z) · X^x · Z^z

so that:
  (0,0) = I,  (1,0) = X,  (0,1) = Z,  (1,1) = iXZ = Y.

An n-qubit Pauli row is the tensor product
  rowPauli x z [k, l] = ∏_j pauliMat(x j, z j)[natBit k j, natBit l j].

A full stabilizer operator (with ±1 phase) is pauliOp.

## Single-qubit Clifford conjugation lemmas

Every 2×2 case is proved by `decide` (all entries are concrete).
These are the eight rules used by the tableau step functions.
-/

namespace LeanQVerify

open Matrix Complex

-- ── Single-qubit Pauli matrices ───────────────────────────────────────────────

/-- Single-qubit Pauli matrix for bits (x, z).
    Convention: (0,0)=I, (1,0)=X, (0,1)=Z, (1,1)=iXZ=Y. -/
noncomputable def pauliMat (x z : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  match x, z with
  | false, false => 1
  | true,  false => X_mat
  | false, true  => Z_mat
  | true,  true  => Complex.I • (X_mat * Z_mat)  -- = Y_mat

theorem pauliMat_II : pauliMat false false = 1               := rfl
theorem pauliMat_XI : pauliMat true  false = X_mat           := rfl
theorem pauliMat_IZ : pauliMat false true  = Z_mat           := rfl
theorem pauliMat_XZ : pauliMat true  true  = Complex.I • (X_mat * Z_mat) := rfl

/-- pauliMat(1,1) equals Y_mat (the standard Pauli-Y). -/
theorem pauliMat_XZ_eq_Y : pauliMat true true = Y_mat := by
  simp only [pauliMat_XZ, Y_mat, X_mat, Z_mat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals ring

-- ── n-qubit Pauli tensor product ──────────────────────────────────────────────

/-- n-qubit Pauli operator for a tableau row: tensor product of single-qubit Paulis.
    Entry (k, l) = ∏_j pauliMat(x j, z j)[natBit k j, natBit l j]. -/
noncomputable def rowPauli {n : ℕ} (x z : Fin n → Bool) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  Matrix.of fun k l =>
    ∏ j : Fin n, pauliMat (x j) (z j) (natBit k.val j.val) (natBit l.val j.val)

/-- Full Pauli operator including ±1 phase: (-1)^phase · rowPauli x z. -/
noncomputable def pauliOp {n : ℕ} (phase : Bool) (x z : Fin n → Bool) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  (if phase then (-1 : ℂ) else 1) • rowPauli x z

-- ── Arithmetic helpers for H-gate conjugation ────────────────────────────────

private lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = (2 : ℂ)⁻¹ := by
  have hsqC : ((Real.sqrt 2 : ℝ) : ℂ) * Real.sqrt 2 = 2 :=
    by exact_mod_cast Real.mul_self_sqrt (by norm_num)
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, hsqC]
  rw [sq]; exact hinv

-- product form (s*s) used for pure-real goals; sq form used after ring_nf
private lemma sqrt2_inv_mul : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← sq]; exact sqrt2_inv_sq

-- ── Single-qubit Clifford conjugation ────────────────────────────────────────

-- H gate: H * pauliMat x z * H = phase_factor • pauliMat z x
-- where phase_factor = -1 when x=1,z=1 and +1 otherwise.

theorem H_conj_II :
    H_mat * (pauliMat false false) * H_mat = pauliMat false false := by
  simp [pauliMat, H_mat_unitary]

theorem H_conj_XI :
    H_mat * (pauliMat true false) * H_mat = pauliMat false true := by
  simp only [pauliMat_XI, pauliMat_IZ]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [H_mat, X_mat, Z_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals (simp only [sqrt2_inv_mul]; norm_num)

theorem H_conj_IZ :
    H_mat * (pauliMat false true) * H_mat = pauliMat true false := by
  simp only [pauliMat_IZ, pauliMat_XI]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [H_mat, X_mat, Z_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals (simp only [sqrt2_inv_mul]; norm_num)

theorem H_conj_XZ :
    H_mat * (pauliMat true true) * H_mat = (-1 : ℂ) • pauliMat true true := by
  simp only [pauliMat_XZ_eq_Y]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [H_mat, Y_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.smul_apply]
  all_goals (ring_nf; simp only [sqrt2_inv_sq]; ring)

-- S gate (H is self-adjoint; S† = [[1,0],[0,-I]])

noncomputable def S_mat_dag : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -Complex.I]

theorem S_dag_eq : S_mat_dag = S_mat.conjTranspose := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [S_mat_dag, S_mat, Matrix.conjTranspose, Matrix.transpose_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.vecHead,
    star_zero, star_one, Complex.star_def, mul_comm]

theorem S_conj_II :
    S_mat * (pauliMat false false) * S_mat.conjTranspose = pauliMat false false := by
  simp only [pauliMat_II, mul_one]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [S_mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
    Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.vecHead, Matrix.one_apply]
  all_goals ring

theorem S_conj_XI :
    S_mat * (pauliMat true false) * S_mat.conjTranspose = pauliMat true true := by
  simp only [pauliMat_XI, pauliMat_XZ_eq_Y]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [S_mat, Y_mat, X_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose, Matrix.transpose_apply, Matrix.vecHead,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals ring

theorem S_conj_IZ :
    S_mat * (pauliMat false true) * S_mat.conjTranspose = pauliMat false true := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [pauliMat, S_mat, Z_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose, Matrix.transpose_apply, Matrix.vecHead,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals ring

theorem S_conj_XZ :
    S_mat * (pauliMat true true) * S_mat.conjTranspose = (-1 : ℂ) • pauliMat true false := by
  simp only [pauliMat_XZ_eq_Y, pauliMat_XI]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [S_mat, Y_mat, X_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose, Matrix.transpose_apply, Matrix.vecHead,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.smul_apply]
  all_goals ring

-- ── n-qubit Clifford conjugation ──────────────────────────────────────────────
-- These are the key lemmas used by stabSim_correct.

/-- Helper: update x-bits for H on qubit a. -/
def xAfterH {n : ℕ} (a : Fin n) (x z : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = a then z a else x j

/-- Helper: update z-bits for H on qubit a. -/
def zAfterH {n : ℕ} (a : Fin n) (x z : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = a then x a else z j

/-- Helper: update x-bits for S on qubit a (unchanged). -/
def xAfterS {n : ℕ} (a : Fin n) (x : Fin n → Bool) : Fin n → Bool := x

/-- Helper: update z-bits for S on qubit a: z[a] ^= x[a]. -/
def zAfterS {n : ℕ} (a : Fin n) (x z : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = a then z a ^^ x a else z j

-- ── Bijection infrastructure ────────────────────────────────────────────────
-- One-sided sum collapse: ∑_m [sameExcept n a m k] * f(m_a) = ∑_b f(b).
-- Mirrors testBit_sum_factoring in Unitary.lean.

private lemma sum_sameExcept {n : ℕ} (a : Fin n) (k : Fin (2^n)) (f : Fin 2 → ℂ) :
    ∑ m : Fin (2^n),
      (if sameExcept n a m k then f (natBit m.val a.val) else 0) =
    ∑ b : Fin 2, f b := by
  have setBit_same : ∀ (v p : ℕ) (b : Bool), (setBit v p b).testBit p = b := by
    intro v p b; unfold setBit; cases b
    · simp [Nat.testBit_ldiff, Nat.shiftLeft_eq, Nat.testBit_two_pow]
    · simp [Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]
  have setBit_ne : ∀ (v p q : ℕ) (b : Bool), q ≠ p →
      (setBit v p b).testBit q = v.testBit q := by
    intro v p q b hqp; unfold setBit; cases b
    · simp [Nat.testBit_ldiff, Nat.shiftLeft_eq, Nat.testBit_two_pow, show p ≠ q from hqp.symm]
    · simp [Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow, show p ≠ q from hqp.symm]
  have setBit_lt : ∀ (v p : ℕ) (b : Bool), v < 2^n → p < n → setBit v p b < 2^n := by
    intro v p b hv hp; unfold setBit; cases b
    · show Nat.ldiff v (1 <<< p) < 2^n
      apply Nat.lt_of_le_of_lt _ hv; apply Nat.le_of_testBit
      intro q hq; simp only [Nat.testBit_ldiff] at hq
      simp only [Bool.and_eq_true] at hq; exact hq.1
    · apply Nat.or_lt_two_pow hv; simp only [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by norm_num) hp
  let mOf (b : Fin 2) : Fin (2^n) :=
    ⟨setBit k.val a.val (b.val == 1), setBit_lt k.val a.val _ k.isLt a.isLt⟩
  have mOf_same : ∀ b : Fin 2, sameExcept n a (mOf b) k :=
    fun b l hl => setBit_ne k.val a.val l.val _ (fun h => hl (Fin.ext h))
  have mOf_bit : ∀ b : Fin 2, natBit (mOf b).val a.val = b := by
    intro b; apply Fin.ext
    have step : (mOf b).val.testBit a.val = (b.val == 1) :=
      setBit_same k.val a.val (b.val == 1)
    simp only [natBit, step]; fin_cases b <;> simp
  have all_from_mOf : ∀ m : Fin (2^n), sameExcept n a m k → m = mOf (natBit m.val a.val) := by
    intro m hm; apply natBit_ext; intro l
    by_cases hla : l = a
    · rw [hla]
      have h1 : (mOf (natBit m.val a.val)).val.testBit a.val =
                (setBit k.val a.val ((natBit m.val a.val).val == 1)).testBit a.val := rfl
      rw [h1, setBit_same]; simp only [natBit]; cases m.val.testBit a.val <;> simp
    · have : (mOf (natBit m.val a.val)).val.testBit l.val = k.val.testBit l.val :=
        setBit_ne k.val a.val l.val _ (fun h => hla (Fin.ext h))
      rw [this]; exact hm l hla
  rw [← Finset.sum_filter]
  apply Finset.sum_bij' (fun m _ => natBit m.val a.val) (fun b _ => mOf b)
  · intro m _; exact Finset.mem_univ _
  · intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mOf_same b⟩
  · intro m hm; rw [Finset.mem_filter] at hm; exact (all_from_mOf m hm.2).symm
  · intro b _; exact mOf_bit b
  · intro m _; rfl

-- Symmetric variant: anchor on the left (sameExcept n a j m).
private lemma sum_sameExcept_symm {n : ℕ} (a : Fin n) (j : Fin (2^n)) (f : Fin 2 → ℂ) :
    ∑ m : Fin (2^n),
      (if sameExcept n a j m then f (natBit m.val a.val) else 0) =
    ∑ b : Fin 2, f b := by
  have iff_sym : ∀ m : Fin (2^n), sameExcept n a j m ↔ sameExcept n a m j :=
    fun m => ⟨fun h l hl => (h l hl).symm, fun h l hl => (h l hl).symm⟩
  simp_rw [iff_sym]
  exact sum_sameExcept a j f

-- Factor rowPauli entry: separate the a-th qubit from the product.
private lemma rowPauli_split_at {n : ℕ} (a : Fin n) (x z : Fin n → Bool) (j k : Fin (2^n)) :
    rowPauli x z j k =
    pauliMat (x a) (z a) (natBit j.val a.val) (natBit k.val a.val) *
    ∏ q ∈ Finset.univ.erase a,
      pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) := by
  simp only [rowPauli, Matrix.of_apply]
  exact (Finset.mul_prod_erase _
    (fun q => pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val))
    (Finset.mem_univ a)).symm

-- Key entry-level factorization: (G ⊗_a) * rowPauli * (G' ⊗_a) entry equals
-- the single-qubit conjugate times the unchanged qubit product.
private lemma embedGate1_conj_entry {n : ℕ} (a : Fin n)
    (G G' : Matrix (Fin 2) (Fin 2) ℂ) (x z : Fin n → Bool) (j k : Fin (2^n)) :
    (embedGate1 n a G * rowPauli x z * embedGate1 n a G') j k =
    (G * pauliMat (x a) (z a) * G') (natBit j.val a.val) (natBit k.val a.val) *
    ∏ q ∈ Finset.univ.erase a,
      pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) := by
  simp only [Matrix.mul_apply, embedGate1, rowPauli, Matrix.of_apply]
  -- LHS = ∑_m (∑_p [jp]*G(ja)(pa)*∏P(p,m)) * [mk]*G'(ma)(ka)
  -- Trans 1: for each m with sameExcept n a m k, collapse the inner sum over p.
  -- Under [jp] and [mk]: ∏P(p,m) = Pa(pa)(ma)*P', so inner = (G*Pa)(ja)(ma)*P'.
  trans (∑ m : Fin (2^n),
    if sameExcept n a m k
    then (G * pauliMat (x a) (z a)) (natBit j.val a.val) (natBit m.val a.val) *
         G' (natBit m.val a.val) (natBit k.val a.val) *
         ∏ q ∈ Finset.univ.erase a,
           pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val)
    else 0)
  · apply Finset.sum_congr rfl; intro m _
    split_ifs with hm
    · -- Collapse inner sum: ∑_p [jp]*G*∏P(p,m) = (G*Pa)(ja)(ma)*P'
      have step1 : ∑ p : Fin (2^n),
          (if sameExcept n a j p then G (natBit j.val a.val) (natBit p.val a.val) else 0) *
          ∏ q, pauliMat (x q) (z q) (natBit p.val q.val) (natBit m.val q.val) =
        (G * pauliMat (x a) (z a)) (natBit j.val a.val) (natBit m.val a.val) *
        ∏ q ∈ Finset.univ.erase a,
          pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) := by
        rw [show ∑ p : Fin (2^n),
              (if sameExcept n a j p then G (natBit j.val a.val) (natBit p.val a.val) else 0) *
              ∏ q, pauliMat (x q) (z q) (natBit p.val q.val) (natBit m.val q.val) =
            ∑ p : Fin (2^n),
              if sameExcept n a j p
              then G (natBit j.val a.val) (natBit p.val a.val) *
                   pauliMat (x a) (z a) (natBit p.val a.val) (natBit m.val a.val) *
                   ∏ q ∈ Finset.univ.erase a,
                     pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val)
              else 0 from by
          apply Finset.sum_congr rfl; intro p _
          split_ifs with hp
          · -- Under hp (p_q=j_q for q≠a) and hm (m_q=k_q for q≠a):
            -- ∏P(p,m) = Pa(pa)(ma) * ∏_{q≠a} P(jq)(kq)
            rw [show ∏ q, pauliMat (x q) (z q) (natBit p.val q.val) (natBit m.val q.val) =
                    pauliMat (x a) (z a) (natBit p.val a.val) (natBit m.val a.val) *
                    ∏ q ∈ Finset.univ.erase a,
                      pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) from by
              rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
              congr 1; apply Finset.prod_congr rfl; intro q hq
              rw [Finset.mem_erase] at hq
              -- Prove natBit equalities separately to avoid dependent rw issue
              have hpj : natBit p.val q.val = natBit j.val q.val := by
                apply Fin.ext; simp only [natBit]; rw [(hp q hq.1).symm]
              have hmk : natBit m.val q.val = natBit k.val q.val := by
                apply Fin.ext; simp only [natBit]; rw [hm q hq.1]
              rw [hpj, hmk]]; ring
          · ring]
        rw [show ∑ p : Fin (2^n),
              (if sameExcept n a j p
               then G (natBit j.val a.val) (natBit p.val a.val) *
                    pauliMat (x a) (z a) (natBit p.val a.val) (natBit m.val a.val) *
                    ∏ q ∈ Finset.univ.erase a,
                      pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val)
               else 0) =
            (∑ p : Fin (2^n),
               if sameExcept n a j p
               then G (natBit j.val a.val) (natBit p.val a.val) *
                    pauliMat (x a) (z a) (natBit p.val a.val) (natBit m.val a.val)
               else 0) *
            ∏ q ∈ Finset.univ.erase a,
              pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) from by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro p _; split_ifs <;> ring]
        rw [sum_sameExcept_symm a j
              (fun b => G (natBit j.val a.val) b *
                        pauliMat (x a) (z a) b (natBit m.val a.val)),
            ← Matrix.mul_apply]
      rw [step1]; ring
    · simp
  · -- Trans 2: collapse outer sum using sum_sameExcept, then use Matrix.mul_apply.
    have collapse := sum_sameExcept a k
        (fun c => (G * pauliMat (x a) (z a)) (natBit j.val a.val) c *
                  G' c (natBit k.val a.val) *
                  ∏ q ∈ Finset.univ.erase a,
                    pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val))
    -- After collapse, the RHS is already in unfolded sum form (from the simp at the top).
    -- Both sides normalize to the same double sum via Matrix.mul_apply + sum_mul.
    rw [collapse]
    simp only [← Finset.sum_mul, Matrix.mul_apply]

/-- H-gate conjugation of a rowPauli:
    (H_a) · rowPauli x z · (H_a) = phase · rowPauli x' z'
    where x'[a]=z[a], z'[a]=x[a], x'[j]=x[j], z'[j]=z[j] for j≠a,
    and phase = -1 if x[a]=1 ∧ z[a]=1, else +1. -/
theorem H_conj_rowPauli {n : ℕ} (a : Fin n) (x z : Fin n → Bool) :
    embedGate1 n a H_mat * rowPauli x z * embedGate1 n a H_mat
    = (if x a && z a then (-1 : ℂ) else 1) • rowPauli (xAfterH a x z) (zAfterH a x z) := by
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [embedGate1_conj_entry a H_mat H_mat x z j k,
      rowPauli_split_at a (xAfterH a x z) (zAfterH a x z) j k]
  -- Show the ∏_{q≠a} factors match (xAfterH/zAfterH q = x q / z q for q ≠ a)
  have prod_eq : ∏ q ∈ Finset.univ.erase a,
      pauliMat (xAfterH a x z q) (zAfterH a x z q) (natBit j.val q.val) (natBit k.val q.val) =
    ∏ q ∈ Finset.univ.erase a,
      pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) := by
    apply Finset.prod_congr rfl; intro q hq
    rw [Finset.mem_erase] at hq
    simp [xAfterH, zAfterH, hq.1]
  rw [prod_eq]
  -- Remaining: (H * P_a * H)(j_a)(k_a) = phase * pauliMat(z a)(x a)(j_a)(k_a)
  -- which follows from the single-qubit conjugation lemmas
  have conj_eq : H_mat * pauliMat (x a) (z a) * H_mat =
      (if x a && z a then (-1 : ℂ) else 1) • pauliMat (z a) (x a) := by
    rcases Bool.eq_false_or_eq_true (x a) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (z a) with hz | hz <;>
    simp [hx, hz, H_conj_II, H_conj_XI, H_conj_IZ, H_conj_XZ]
  have hxa : xAfterH a x z a = z a := by simp [xAfterH]
  have hza : zAfterH a x z a = x a := by simp [zAfterH]
  rw [hxa, hza, conj_eq, Matrix.smul_apply]
  ring

/-- S-gate conjugation of a rowPauli:
    (S_a) · rowPauli x z · (S_a†) = phase · rowPauli x' z'
    where x'=x, z'[a]=z[a]^x[a], z'[j]=z[j] for j≠a,
    and phase = -1 if x[a]=1 ∧ z[a]=1, else +1. -/
theorem S_conj_rowPauli {n : ℕ} (a : Fin n) (x z : Fin n → Bool) :
    embedGate1 n a S_mat * rowPauli x z * embedGate1 n a S_mat.conjTranspose
    = (if x a && z a then (-1 : ℂ) else 1) • rowPauli (xAfterS a x) (zAfterS a x z) := by
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [embedGate1_conj_entry a S_mat S_mat.conjTranspose x z j k,
      rowPauli_split_at a (xAfterS a x) (zAfterS a x z) j k]
  have prod_eq : ∏ q ∈ Finset.univ.erase a,
      pauliMat (xAfterS a x q) (zAfterS a x z q) (natBit j.val q.val) (natBit k.val q.val) =
    ∏ q ∈ Finset.univ.erase a,
      pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) := by
    apply Finset.prod_congr rfl; intro q hq
    rw [Finset.mem_erase] at hq
    simp [xAfterS, zAfterS, hq.1]
  rw [prod_eq]
  have conj_eq : S_mat * pauliMat (x a) (z a) * S_mat.conjTranspose =
      (if x a && z a then (-1 : ℂ) else 1) • pauliMat (x a) (z a ^^ x a) := by
    rcases Bool.eq_false_or_eq_true (x a) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (z a) with hz | hz <;>
    simp [hx, hz, S_conj_II, S_conj_XI, S_conj_IZ, S_conj_XZ]
  -- xAfterS a x = x by definition; zAfterS a x z a = z a ^^ x a by if_pos rfl.
  -- Use simp only to rewrite these in-goal (avoid Bool normalization of a standalone have).
  have xsa : xAfterS a x a = x a := rfl
  simp only [xsa, zAfterS, eq_self_iff_true, if_true]
  rw [conj_eq, Matrix.smul_apply]
  ring

-- ── X and Z conjugation of rowPauli ─────────────────────────────────────────

/-- X-gate conjugation of a rowPauli:
    (X_a) · rowPauli x z · (X_a) = phase · rowPauli x z
    where phase = -1 if z[a]=1, else +1. -/
theorem X_conj_rowPauli {n : ℕ} (a : Fin n) (x z : Fin n → Bool) :
    embedGate1 n a X_mat * rowPauli x z * embedGate1 n a X_mat
    = (if z a then (-1 : ℂ) else 1) • rowPauli x z := by
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [embedGate1_conj_entry a X_mat X_mat x z j k,
      rowPauli_split_at a x z j k]
  have conj_eq : X_mat * pauliMat (x a) (z a) * X_mat =
      (if z a then (-1 : ℂ) else 1) • pauliMat (x a) (z a) := by
    rcases Bool.eq_false_or_eq_true (x a) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (z a) with hz | hz <;>
    simp only [hx, hz, pauliMat_II, pauliMat_XI, pauliMat_IZ, pauliMat_XZ_eq_Y, if_true, if_false] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [X_mat, Z_mat, Y_mat, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.smul_apply] <;> ring
  rw [conj_eq, Matrix.smul_apply]
  ring

/-- Z-gate conjugation of a rowPauli:
    (Z_a) · rowPauli x z · (Z_a) = phase · rowPauli x z
    where phase = -1 if x[a]=1, else +1. -/
theorem Z_conj_rowPauli {n : ℕ} (a : Fin n) (x z : Fin n → Bool) :
    embedGate1 n a Z_mat * rowPauli x z * embedGate1 n a Z_mat
    = (if x a then (-1 : ℂ) else 1) • rowPauli x z := by
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [embedGate1_conj_entry a Z_mat Z_mat x z j k,
      rowPauli_split_at a x z j k]
  have conj_eq : Z_mat * pauliMat (x a) (z a) * Z_mat =
      (if x a then (-1 : ℂ) else 1) • pauliMat (x a) (z a) := by
    rcases Bool.eq_false_or_eq_true (x a) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (z a) with hz | hz <;>
    simp only [hx, hz, pauliMat_II, pauliMat_XI, pauliMat_IZ, pauliMat_XZ_eq_Y, if_true, if_false] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [X_mat, Z_mat, Y_mat, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.smul_apply] <;> ring
  rw [conj_eq, Matrix.smul_apply]
  ring

-- ── CNOT conjugation helpers ─────────────────────────────────────────────────

private lemma cnotFn_lt_t {n : ℕ} (a b : Fin n) (j : Fin (2^n)) :
    (if j.val.testBit a.val then j.val ^^^ (1 <<< b.val) else j.val) < 2^n := by
  split
  · exact Nat.xor_lt_two_pow j.isLt
        (by simp [Nat.shiftLeft_eq]; exact Nat.pow_lt_pow_right (by norm_num) b.isLt)
  · exact j.isLt

private def cnotFn' {n : ℕ} (a b : Fin n) (j : Fin (2^n)) : Fin (2^n) :=
  ⟨if j.val.testBit a.val then j.val ^^^ (1 <<< b.val) else j.val, cnotFn_lt_t a b j⟩

private lemma testBit_shift_ne' {q b : ℕ} (h : q ≠ b) : (1 <<< b).testBit q = false := by
  simp only [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]; simp [Ne.symm h]

private lemma testBit_shift_self' (b : ℕ) : (1 <<< b).testBit b = true := by
  simp [Nat.shiftLeft_eq]

private lemma cnotFn_invol' {n : ℕ} (a b : Fin n) (hab : a ≠ b) (j : Fin (2^n)) :
    cnotFn' a b (cnotFn' a b j) = j := by
  have hb_bit := testBit_shift_ne' (Fin.val_ne_of_ne hab)
  have xor_a : ∀ v : ℕ, (v ^^^ 1 <<< b.val).testBit a.val = v.testBit a.val := fun v => by
    rw [Nat.testBit_xor, hb_bit, Bool.xor_false]
  simp only [cnotFn', Fin.ext_iff, Fin.val_mk]
  by_cases hj : j.val.testBit a.val
  · simp [hj, xor_a]
  · simp [hj]

private lemma embedCNOT_apply_cnotFn' {n : ℕ} (a b : Fin n) (u v : Fin (2^n)) :
    (embedCNOT n a b u v : ℂ) = if v = cnotFn' a b u then 1 else 0 := by
  simp only [embedCNOT, cnotFn', Fin.ext_iff]

private lemma embedCNOT_conj_apply_t' {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (M : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (j k : Fin (2^n)) :
    (embedCNOT n a b * M * embedCNOT n a b) j k = M (cnotFn' a b j) (cnotFn' a b k) := by
  have invol_iff : ∀ m' : Fin (2^n), k = cnotFn' a b m' ↔ m' = cnotFn' a b k := fun m' =>
    ⟨fun h => by
      have h1 := congr_arg (cnotFn' a b) h.symm
      rw [cnotFn_invol' a b hab] at h1; exact h1,
    fun h => by
      have h1 := congr_arg (cnotFn' a b) h.symm
      rw [cnotFn_invol' a b hab] at h1; exact h1⟩
  simp only [Matrix.mul_apply, embedCNOT_apply_cnotFn']
  have ite_mul : ∀ (m1 m2 : Fin (2^n)),
      (if m2 = cnotFn' a b j then (1:ℂ) else 0) * M m2 m1 =
      if m2 = cnotFn' a b j then M m2 m1 else 0 := fun m1 m2 => by split_ifs <;> ring
  simp_rw [ite_mul, Finset.sum_ite_eq' Finset.univ (cnotFn' a b j) _, Finset.mem_univ, if_true]
  have mul_ite : ∀ (m1 : Fin (2^n)),
      M (cnotFn' a b j) m1 * (if k = cnotFn' a b m1 then (1:ℂ) else 0) =
      if m1 = cnotFn' a b k then M (cnotFn' a b j) m1 else 0 := fun m1 => by
    by_cases h : m1 = cnotFn' a b k
    · simp only [if_pos h, if_pos ((invol_iff m1).mpr h)]; ring
    · simp only [if_neg h, if_neg (fun hk => h ((invol_iff m1).mp hk))]; ring
  simp_rw [mul_ite, Finset.sum_ite_eq' Finset.univ (cnotFn' a b k) _, Finset.mem_univ, if_true]

private lemma natBit_cnotFn_non_b' {n : ℕ} (a b : Fin n) (j : Fin (2^n)) {q : Fin n}
    (hq : q ≠ b) : natBit (cnotFn' a b j).val q.val = natBit j.val q.val := by
  have hq_bit := testBit_shift_ne' (Fin.val_ne_of_ne hq)
  simp only [natBit, cnotFn', Fin.val_mk]
  by_cases hj : j.val.testBit a.val
  · simp [hj, Nat.testBit_xor, hq_bit]
  · simp [hj]

private lemma fin2_xor_lt'' (a b : Fin 2) : a.val ^^^ b.val < 2 := by
  fin_cases a <;> fin_cases b <;> simp

private lemma natBit_cnotFn_b' {n : ℕ} (a b : Fin n) (j : Fin (2^n)) :
    natBit (cnotFn' a b j).val b.val =
    ⟨(natBit j.val a.val).val ^^^ (natBit j.val b.val).val, fin2_xor_lt'' _ _⟩ := by
  have hb_self := testBit_shift_self' b.val
  simp only [natBit, cnotFn', Fin.val_mk, Fin.ext_iff]
  rcases Bool.eq_false_or_eq_true (j.val.testBit a.val) with hja | hja <;>
  rcases Bool.eq_false_or_eq_true (j.val.testBit b.val) with hjb | hjb <;>
  simp [hja, hjb, Nat.testBit_xor, hb_self]

private lemma cnot_pauli_2qubit' (xa za xb zb : Bool) (ja ka jb kb : Fin 2) :
    pauliMat xb zb ⟨ja.val ^^^ jb.val, fin2_xor_lt'' ja jb⟩
                   ⟨ka.val ^^^ kb.val, fin2_xor_lt'' ka kb⟩ *
    pauliMat xa za ja ka
    = (if xa && zb && (xb ^^ za ^^ true) then (-1 : ℂ) else 1) *
      (pauliMat xa (za ^^ zb) ja ka * pauliMat (xb ^^ xa) zb jb kb) := by
  rcases Bool.eq_false_or_eq_true xa with hxa | hxa <;>
  rcases Bool.eq_false_or_eq_true za with hza | hza <;>
  rcases Bool.eq_false_or_eq_true xb with hxb | hxb <;>
  rcases Bool.eq_false_or_eq_true zb with hzb | hzb <;>
  simp only [hxa, hza, hxb, hzb, pauliMat_II, pauliMat_XI, pauliMat_IZ, pauliMat_XZ,
    Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true,
    Bool.xor_false, Bool.false_xor, Bool.true_xor, Bool.xor_true, if_true, if_false] <;>
  fin_cases ja <;> fin_cases ka <;> fin_cases jb <;> fin_cases kb <;>
  simp [X_mat, Z_mat, Complex.I_mul_I, Matrix.one_apply] <;>
  simp [pauliMat, X_mat, Z_mat]

/-- CNOT conjugation of a rowPauli (control=a, target=b, requires a ≠ b):
    Pauli update rules per Aaronson–Gottesman Table 1:
      x'[a] = x[a],       z'[a] = z[a] ^ z[b]
      x'[b] = x[b] ^ x[a], z'[b] = z[b]
    phase change: r ^^ (x[a] && z[b] && (x[b] ^^ z[a] ^^ true)). -/
theorem CNOT_conj_rowPauli {n : ℕ} (a b : Fin n) (hab : a ≠ b) (x z : Fin n → Bool) :
    embedCNOT n a b * rowPauli x z * embedCNOT n a b
    = (if x a && z b && (x b ^^ z a ^^ true) then (-1 : ℂ) else 1) •
      rowPauli (fun j => if j = b then x j ^^ x a else x j)
               (fun j => if j = a then z j ^^ z b else z j) := by
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul, rowPauli, Matrix.of_apply]
  rw [embedCNOT_conj_apply_t' a b hab]
  simp only [Matrix.of_apply]
  set ja := natBit j.val a.val with ja_def
  set ka := natBit k.val a.val with ka_def
  set jb := natBit j.val b.val with jb_def
  set kb := natBit k.val b.val with kb_def
  have hja : natBit (cnotFn' a b j).val a.val = ja := natBit_cnotFn_non_b' a b j hab
  have hka : natBit (cnotFn' a b k).val a.val = ka := natBit_cnotFn_non_b' a b k hab
  have hjb' : natBit (cnotFn' a b j).val b.val =
      ⟨ja.val ^^^ jb.val, fin2_xor_lt'' ja jb⟩ := natBit_cnotFn_b' a b j
  have hkb' : natBit (cnotFn' a b k).val b.val =
      ⟨ka.val ^^^ kb.val, fin2_xor_lt'' ka kb⟩ := natBit_cnotFn_b' a b k
  have lhs_eq : ∏ q : Fin n,
        pauliMat (x q) (z q) (natBit (cnotFn' a b j).val q.val) (natBit (cnotFn' a b k).val q.val) =
      pauliMat (x a) (z a) ja ka *
      (pauliMat (x b) (z b) ⟨ja.val ^^^ jb.val, fin2_xor_lt'' ja jb⟩ ⟨ka.val ^^^ kb.val, fin2_xor_lt'' ka kb⟩ *
       ∏ q ∈ (Finset.univ.erase a).erase b,
         pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
    congr 1
    · rw [hja, hka]
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
      congr 1
      · rw [hjb', hkb']
      · apply Finset.prod_congr rfl; intro q hq
        rw [Finset.mem_erase] at hq
        rw [natBit_cnotFn_non_b' a b j hq.1, natBit_cnotFn_non_b' a b k hq.1]
  have rhs_eq : ∏ q : Fin n,
        pauliMat (if q = b then x q ^^ x a else x q) (if q = a then z q ^^ z b else z q)
        (natBit j.val q.val) (natBit k.val q.val) =
      pauliMat (x a) (z a ^^ z b) ja ka *
      (pauliMat (x b ^^ x a) (z b) jb kb *
       ∏ q ∈ (Finset.univ.erase a).erase b,
         pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
    congr 1
    · simp only [if_neg hab, if_true, ← ja_def, ← ka_def]
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
      congr 1
      · simp only [if_true, if_neg (Ne.symm hab), ← jb_def, ← kb_def]
      · apply Finset.prod_congr rfl; intro q hq
        rw [Finset.mem_erase] at hq
        have hqa : q ≠ a := (Finset.mem_erase.mp hq.2).1
        simp [hq.1, hqa]
  rw [lhs_eq, rhs_eq]
  have key := cnot_pauli_2qubit' (x a) (z a) (x b) (z b) ja ka jb kb
  have comm_step : pauliMat (x a) (z a) ja ka *
        (pauliMat (x b) (z b) ⟨ja.val ^^^ jb.val, fin2_xor_lt'' ja jb⟩ ⟨ka.val ^^^ kb.val, fin2_xor_lt'' ka kb⟩ *
         ∏ q ∈ (Finset.univ.erase a).erase b,
           pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val)) =
        (pauliMat (x b) (z b) ⟨ja.val ^^^ jb.val, fin2_xor_lt'' ja jb⟩ ⟨ka.val ^^^ kb.val, fin2_xor_lt'' ka kb⟩ *
         pauliMat (x a) (z a) ja ka) *
         ∏ q ∈ (Finset.univ.erase a).erase b,
           pauliMat (x q) (z q) (natBit j.val q.val) (natBit k.val q.val) := by ring
  rw [comm_step, key]
  ring

end LeanQVerify
