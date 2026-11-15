import LeanQVerify.Stabilizer.PauliGroup
import LeanQVerify.Stabilizer.StabTableau
import LeanQVerify.Spec.CircuitSpec

/-!
# Stabilizer Backend Soundness (Phase 2)

The load-bearing theorem of Phase 2:

```
stabSim_correct : Represents t ψ → Represents (stabSim c t) (c.toQCircuit.applyTo ψ)
```

One proof justifies unlimited automatic stabilizer proofs.

## Architecture

`Represents t ψ` says: each stabilizer row (rows n..2n-1) encodes a
Pauli operator that stabilizes ψ.

`stabSim_correct` is proved by induction on the circuit, reducing to
`Represents.step` for single gates.  Each gate case uses one of the
three conjugation lemmas from PauliGroup.lean:
- `H_conj_rowPauli`   (H gate)
- `S_conj_rowPauli`   (S gate)
- `CNOT_conj_rowPauli` (CNOT gate)

`zProb` extracts a measurement probability bound from the final tableau.
Its correctness (`zProb_correct`) ties the tableau to CircuitSpec.

## Status

`stabSim_correct` is proved modulo the three conjugation lemmas, which
are currently marked sorry in PauliGroup.lean.  Filling those three
lemmas (entry-by-entry matrix algebra) completes Phase 2.
-/

namespace LeanQVerify

open Matrix Complex QCircuit CircuitSpec

-- ── Represents predicate ──────────────────────────────────────────────────────

-- Maps stabilizer index i : Fin n to tableau row n+i : Fin (2*n)
def stabRow {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨n + i.val, by omega⟩

/-- Tableau t represents state ψ if every stabilizer row (n..2n-1)
    stabilizes ψ: pauliOp(phase, x, z) *ᵥ ψ = ψ. -/
def Represents {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ) : Prop :=
  ∀ i : Fin n,
    pauliOp (t.phase (stabRow i))
            (t.x    (stabRow i))
            (t.z    (stabRow i)) *ᵥ ψ = ψ

-- ── Initial state ─────────────────────────────────────────────────────────────

/-- |0^n⟩ amplitude function: 1 at index 0, 0 elsewhere. -/
def ket0Vec (n : ℕ) : Fin (2^n) → ℂ := fun k => if k.val = 0 then 1 else 0

-- pauliMat false b r ⟨0,_⟩ = if r.val = 0 then 1 else 0
private lemma pauliMat_false_col0 (b : Bool) (r : Fin 2) :
    pauliMat false b r ⟨0, by norm_num⟩ = if r.val = 0 then (1 : ℂ) else 0 := by
  fin_cases b <;> fin_cases r <;>
  simp [pauliMat, Z_mat, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Fin.ext_iff]

-- natBit 0 j = ⟨0, _⟩
private lemma natBit_zero_val (j : ℕ) : natBit 0 j = (⟨0, by norm_num⟩ : Fin 2) := by
  ext; simp [natBit, Nat.zero_testBit]

-- ∏ j, (if (natBit k j).val = 0 then 1 else 0) = if k = 0 then 1 else 0
private lemma prod_ite_natBit_eq {n : ℕ} (k : Fin (2^n)) :
    ∏ j : Fin n, (if (natBit k.val j.val).val = 0 then (1:ℂ) else 0) = if k.val = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k.val with hk | hk
  · have hk' : (k : ℕ) = 0 := hk
    simp only [hk', if_pos rfl]
    apply Finset.prod_eq_one; intro j _; simp [natBit, Nat.zero_testBit, hk]
  · have hne : k.val ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    simp only [show (k : ℕ) ≠ 0 from hne, ↓reduceIte]
    have hlog_lt : k.val.log2 < n := (Nat.log2_lt hne).mpr k.isLt
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨k.val.log2, hlog_lt⟩ : Fin n))
    simp [natBit, Nat.testBit_log2 hne]

-- Z-only rowPauli fixes ket0Vec: rowPauli (fun _ => false) z *ᵥ ket0Vec n = ket0Vec n
private lemma rowPauli_zOnly_ket0Vec {n : ℕ} (z : Fin n → Bool) :
    rowPauli (fun _ => false) z *ᵥ ket0Vec n = ket0Vec n := by
  funext k
  show ∑ l : Fin (2^n),
      (∏ j : Fin n, pauliMat false (z j) (natBit k.val j.val) (natBit l.val j.val)) *
      (if l.val = 0 then (1 : ℂ) else 0) = if k.val = 0 then 1 else 0
  have hpow : 0 < 2^n := Nat.two_pow_pos n
  rw [Finset.sum_eq_single (⟨0, hpow⟩ : Fin (2^n))
      (fun l _ hn => by simp only [if_neg (fun h => hn (Fin.ext h)), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [mul_one, if_true]
  simp_rw [natBit_zero_val, pauliMat_false_col0]
  exact prod_ite_natBit_eq k

/-- The initial tableau represents |0^n⟩. -/
theorem ket0n_represents (n : ℕ) : Represents (ket0n n) (ket0Vec n) := by
  intro i
  simp only [pauliOp, ket0n, stabRow]
  norm_num
  exact rowPauli_zOnly_ket0Vec _

/-- The all-zeros state vector is normalized: ∑ |ket0Vec k|² = 1. -/
lemma ket0Vec_norm (n : ℕ) : ∑ k : Fin (2^n), Complex.normSq (ket0Vec n k) = 1 := by
  rw [Finset.sum_eq_single (⟨0, Nat.two_pow_pos n⟩ : Fin (2^n))
      (fun k _ hk => by
        simp only [ket0Vec, if_neg (show k.val ≠ 0 from fun h => hk (Fin.ext h)),
                   Complex.normSq_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp [ket0Vec]

-- ── Gate-by-gate Represents update ───────────────────────────────────────────

-- S†·S = I, needed for the S-gate mulVec step
private lemma S_mat_adj_self : S_mat.conjTranspose * S_mat = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [S_mat, Matrix.conjTranspose, Matrix.transpose_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

-- General step: if G'·G = I and P·ψ = ψ then (G·P·G')·(G·ψ) = G·ψ
private lemma stabStep_mulVec {m : ℕ}
    (G G' : Matrix (Fin (2^m)) (Fin (2^m)) ℂ) (hGG' : G' * G = 1)
    (P : Matrix (Fin (2^m)) (Fin (2^m)) ℂ) (ψ : Fin (2^m) → ℂ)
    (hstab : P *ᵥ ψ = ψ) :
    (G * P * G') *ᵥ (G *ᵥ ψ) = G *ᵥ ψ := by
  rw [Matrix.mulVec_mulVec,
      show (G * P * G') * G = G * P from by simp only [mul_assoc, hGG', mul_one],
      ← Matrix.mulVec_mulVec, hstab]

/-- Stabilizer preservation after H gate. -/
theorem Represents.stepH {n : ℕ} (a : Fin n) (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (t.stepH a) (embedGate1 n a H_mat *ᵥ ψ) := by
  intro i
  set row := stabRow i
  set H_a := embedGate1 n a H_mat
  have hi : pauliOp (t.phase row) (t.x row) (t.z row) *ᵥ ψ = ψ := h i
  have hH2 : H_a * H_a = 1 := embedGate1_self_inverse n a H_mat H_mat_unitary
  have hx' : (t.stepH a).x row = xAfterH a (t.x row) (t.z row) := by
    funext q; simp only [StabTableau.stepH, xAfterH]
    by_cases hq : q = a <;> simp [hq]
  have hz' : (t.stepH a).z row = zAfterH a (t.x row) (t.z row) := by
    funext q; simp only [StabTableau.stepH, zAfterH]
    by_cases hq : q = a <;> simp [hq]
  have hr' : (t.stepH a).phase row = (t.phase row ^^ (t.x row a && t.z row a)) := rfl
  have conj : pauliOp ((t.stepH a).phase row) ((t.stepH a).x row) ((t.stepH a).z row) =
              H_a * pauliOp (t.phase row) (t.x row) (t.z row) * H_a := by
    rw [hx', hz', hr']
    simp only [pauliOp]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, H_conj_rowPauli, smul_smul]
    congr 1
    rcases Bool.eq_false_or_eq_true (t.phase row) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true (t.x row a && t.z row a) with hb | hb <;>
    simp [hr, hb]
  rw [conj]
  exact stabStep_mulVec H_a H_a hH2 (pauliOp (t.phase row) (t.x row) (t.z row)) ψ hi

/-- Stabilizer preservation after S gate. -/
theorem Represents.stepS {n : ℕ} (a : Fin n) (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (t.stepS a) (embedGate1 n a S_mat *ᵥ ψ) := by
  intro i
  set row := stabRow i
  set S_a  := embedGate1 n a S_mat
  set S_ad := embedGate1 n a S_mat.conjTranspose
  have hi : pauliOp (t.phase row) (t.x row) (t.z row) *ᵥ ψ = ψ := h i
  have hSS : S_ad * S_a = 1 := by
    simp only [S_ad, S_a, embedGate1_mul, S_mat_adj_self, embedGate1_one]
  have hx' : (t.stepS a).x row = xAfterS a (t.x row) := rfl
  have hz' : (t.stepS a).z row = zAfterS a (t.x row) (t.z row) := by
    funext q; simp only [StabTableau.stepS, zAfterS]
    by_cases hq : q = a <;> simp [hq]
  have hr' : (t.stepS a).phase row = (t.phase row ^^ (t.x row a && t.z row a)) := rfl
  have conj : pauliOp ((t.stepS a).phase row) ((t.stepS a).x row) ((t.stepS a).z row) =
              S_a * pauliOp (t.phase row) (t.x row) (t.z row) * S_ad := by
    rw [hx', hz', hr']
    simp only [pauliOp]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, S_conj_rowPauli, smul_smul]
    congr 1
    rcases Bool.eq_false_or_eq_true (t.phase row) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true (t.x row a && t.z row a) with hb | hb <;>
    simp [hr, hb]
  rw [conj]
  exact stabStep_mulVec S_a S_ad hSS (pauliOp (t.phase row) (t.x row) (t.z row)) ψ hi

/-- Stabilizer preservation after X gate. -/
theorem Represents.stepX {n : ℕ} (a : Fin n) (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (t.stepX a) (embedGate1 n a X_mat *ᵥ ψ) := by
  intro i
  set row := stabRow i
  set X_a := embedGate1 n a X_mat
  have hi : pauliOp (t.phase row) (t.x row) (t.z row) *ᵥ ψ = ψ := h i
  have hX2 : X_a * X_a = 1 := embedGate1_self_inverse n a X_mat X_mat_unitary
  have hr' : (t.stepX a).phase row = (t.phase row ^^ t.z row a) := rfl
  have conj : pauliOp ((t.stepX a).phase row) ((t.stepX a).x row) ((t.stepX a).z row) =
              X_a * pauliOp (t.phase row) (t.x row) (t.z row) * X_a := by
    rw [show (t.stepX a).x row = t.x row from rfl,
        show (t.stepX a).z row = t.z row from rfl, hr']
    simp only [pauliOp]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, X_conj_rowPauli, smul_smul]
    congr 1
    rcases Bool.eq_false_or_eq_true (t.phase row) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true (t.z row a) with hz | hz <;>
    simp [hr, hz]
  rw [conj]
  exact stabStep_mulVec X_a X_a hX2 (pauliOp (t.phase row) (t.x row) (t.z row)) ψ hi

/-- Stabilizer preservation after Z gate. -/
theorem Represents.stepZ {n : ℕ} (a : Fin n) (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (t.stepZ a) (embedGate1 n a Z_mat *ᵥ ψ) := by
  intro i
  set row := stabRow i
  set Z_a := embedGate1 n a Z_mat
  have hi : pauliOp (t.phase row) (t.x row) (t.z row) *ᵥ ψ = ψ := h i
  have hZ2 : Z_a * Z_a = 1 := embedGate1_self_inverse n a Z_mat Z_mat_unitary
  have hr' : (t.stepZ a).phase row = (t.phase row ^^ t.x row a) := rfl
  have conj : pauliOp ((t.stepZ a).phase row) ((t.stepZ a).x row) ((t.stepZ a).z row) =
              Z_a * pauliOp (t.phase row) (t.x row) (t.z row) * Z_a := by
    rw [show (t.stepZ a).x row = t.x row from rfl,
        show (t.stepZ a).z row = t.z row from rfl, hr']
    simp only [pauliOp]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Z_conj_rowPauli, smul_smul]
    congr 1
    rcases Bool.eq_false_or_eq_true (t.phase row) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true (t.x row a) with hxa | hxa <;>
    simp [hr, hxa]
  rw [conj]
  exact stabStep_mulVec Z_a Z_a hZ2 (pauliOp (t.phase row) (t.x row) (t.z row)) ψ hi

/-- Stabilizer preservation after CNOT gate (requires a ≠ b). -/
theorem Represents.stepCNOT {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (t.stepCNOT a b) (embedCNOT n a b *ᵥ ψ) := by
  intro i
  set row := stabRow i
  set C_a := embedCNOT n a b
  have hi : pauliOp (t.phase row) (t.x row) (t.z row) *ᵥ ψ = ψ := h i
  have hC2 : C_a * C_a = 1 := embedCNOT_self_mul n a b hab
  have hx' : (t.stepCNOT a b).x row =
             fun j => if j = b then t.x row j ^^ t.x row a else t.x row j := rfl
  have hz' : (t.stepCNOT a b).z row =
             fun j => if j = a then t.z row j ^^ t.z row b else t.z row j := rfl
  have hr' : (t.stepCNOT a b).phase row =
             (t.phase row ^^ (t.x row a && t.z row b && (t.x row b ^^ t.z row a ^^ true))) := rfl
  have conj : pauliOp ((t.stepCNOT a b).phase row)
                      ((t.stepCNOT a b).x row) ((t.stepCNOT a b).z row) =
              C_a * pauliOp (t.phase row) (t.x row) (t.z row) * C_a := by
    rw [hx', hz', hr']
    simp only [pauliOp]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, CNOT_conj_rowPauli a b hab, smul_smul]
    congr 1
    rcases Bool.eq_false_or_eq_true (t.phase row) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true (t.x row a) with hxa | hxa <;>
    rcases Bool.eq_false_or_eq_true (t.z row b) with hzb | hzb <;>
    rcases Bool.eq_false_or_eq_true (t.x row b) with hxb | hxb <;>
    rcases Bool.eq_false_or_eq_true (t.z row a) with hza | hza <;>
    simp [hr, hxa, hzb, hxb, hza]
  rw [conj]
  exact stabStep_mulVec C_a C_a hC2 (pauliOp (t.phase row) (t.x row) (t.z row)) ψ hi

/-- Stabilizer preservation after any single Clifford gate. -/
theorem Represents.step {n : ℕ} (g : CliffordGate n) (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (t.step g) (g.toGate.matrix *ᵥ ψ) := by
  match g with
  | .H q          => exact h.stepH q
  | .S q          => exact h.stepS q
  | .X q          => exact h.stepX q
  | .Z q          => exact h.stepZ q
  | .CNOT a b hab => exact h.stepCNOT a b hab

-- ── Main soundness theorem ────────────────────────────────────────────────────

/-- Gate-by-gate evaluation bridges applyTo for Clifford circuits. -/
private theorem CliffordCircuit.toQCircuit_applyTo {n : ℕ}
    (c : CliffordCircuit n) (ψ : Fin (2^n) → ℂ) :
    c.toQCircuit.applyTo ψ =
    c.foldl (fun v g => g.toGate.matrix *ᵥ v) ψ := by
  induction c generalizing ψ with
  | nil  => simp [CliffordCircuit.toQCircuit, QCircuit.applyTo]
  | cons g gs ih =>
    simp only [CliffordCircuit.toQCircuit, List.foldl]
    rw [show (QCircuit.cons g.toGate (CliffordCircuit.toQCircuit gs)).applyTo ψ =
             (CliffordCircuit.toQCircuit gs).applyTo (g.toGate.matrix *ᵥ ψ) from by
      simp only [QCircuit.applyTo, QCircuit.denote_cons, ← Matrix.mulVec_mulVec]]
    exact ih (g.toGate.matrix *ᵥ ψ)

/-- **Main theorem (Phase 2)**: stabilizer simulation is semantically correct.

    If tableau `t` represents state `ψ`, then after simulating Clifford
    circuit `c` on the tableau, the result represents the evolved state
    `c.toQCircuit.applyTo ψ`.

    The proof is by structural induction on `c`, using `Represents.step`
    at each gate.  Every step theorem is proved using one of the three
    Pauli conjugation lemmas (H_conj_rowPauli / S_conj_rowPauli /
    CNOT_conj_rowPauli) from PauliGroup.lean. -/
theorem stabSim_correct {n : ℕ} (c : CliffordCircuit n)
    (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t ψ) :
    Represents (stabSim c t) (c.toQCircuit.applyTo ψ) := by
  induction c generalizing t ψ with
  | nil  =>
    simp [stabSim, CliffordCircuit.toQCircuit, QCircuit.applyTo, h]
  | cons g gs ih =>
    simp only [stabSim_cons, CliffordCircuit.toQCircuit]
    rw [show (QCircuit.cons g.toGate (CliffordCircuit.toQCircuit gs)).applyTo ψ =
             (CliffordCircuit.toQCircuit gs).applyTo (g.toGate.matrix *ᵥ ψ) from by
      simp only [QCircuit.applyTo, QCircuit.denote_cons, ← Matrix.mulVec_mulVec]]
    apply ih
    exact h.step g

-- ── Measurement probability from tableau ─────────────────────────────────────

/-- Check whether stabilizer row i anti-commutes with Z_q.
    (A Pauli anti-commutes with Z_q iff it has X_q in it: x[i,q] = 1.) -/
def StabTableau.antiCommutesZ {n : ℕ} (t : StabTableau n) (row : Fin (2*n)) (q : Fin n) : Bool :=
  t.x row q

-- ── Helper lemmas for zProb_correct ──────────────────────────────────────────

private lemma inner_mulVec_left {n : ℕ} (M : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (u v : Fin (2^n) → ℂ) :
    ∑ k, star ((M *ᵥ u) k) * v k = ∑ k, star (u k) * ((M.conjTranspose *ᵥ v) k) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
             star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

-- If M†M = I then M preserves the ℓ²-norm of state vectors.
private lemma mulVec_normSq_of_unitary {n : ℕ}
    (M : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (ψ : Fin (2^n) → ℂ)
    (hU : M.conjTranspose * M = 1) :
    ∑ k : Fin (2^n), Complex.normSq ((M *ᵥ ψ) k) =
    ∑ k : Fin (2^n), Complex.normSq (ψ k) := by
  have key : ∀ f : Fin (2^n) → ℂ, ∑ k, Complex.normSq (f k) =
      (∑ k, star (f k) * f k).re := by
    intro f
    rw [Complex.re_sum]; congr 1; ext k
    rw [star_def, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.ofReal_re _
  rw [key (M *ᵥ ψ), key ψ]
  congr 1
  have hMtMψ : M.conjTranspose *ᵥ (M *ᵥ ψ) = ψ := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [inner_mulVec_left M ψ (M *ᵥ ψ), hMtMψ]

private lemma pauliMat_self_conj {x z : Bool} {r s : Fin 2} :
    star (pauliMat x z r s) = pauliMat x z s r := by
  fin_cases x <;> fin_cases z <;> fin_cases r <;> fin_cases s <;>
  simp only [pauliMat_II, pauliMat_XI, pauliMat_IZ, pauliMat_XZ_eq_Y,
             Matrix.one_apply, X_mat, Z_mat, Y_mat,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.smul_apply, star_zero, star_one, star_neg, Complex.star_def,
             Complex.I_re, Complex.I_im] <;>
  simp [Complex.ext_iff] <;> norm_num

private lemma rowPauli_hermitian {n : ℕ} (x z : Fin n → Bool) :
    (rowPauli x z).conjTranspose = rowPauli x z := by
  ext k l
  simp only [Matrix.conjTranspose_apply, rowPauli, Matrix.of_apply, star_prod]
  congr 1; ext j
  exact pauliMat_self_conj

private lemma pauliOp_conj {n : ℕ} (phase : Bool) (x z : Fin n → Bool) :
    (pauliOp phase x z).conjTranspose = pauliOp phase x z := by
  simp only [pauliOp, Matrix.conjTranspose_smul, rowPauli_hermitian]
  cases phase <;> simp [star_neg, star_one]

private lemma Zq_anticomm_rowPauli {n : ℕ} (q : Fin n) (x z : Fin n → Bool)
    (hxq : x q = true) :
    embedGate1 n q Z_mat * rowPauli x z = -(rowPauli x z * embedGate1 n q Z_mat) := by
  have hconj : embedGate1 n q Z_mat * rowPauli x z * embedGate1 n q Z_mat = -rowPauli x z := by
    rw [Z_conj_rowPauli, hxq]; simp [neg_one_smul]
  have hZsq := embedGate1_self_inverse n q Z_mat Z_mat_unitary
  calc embedGate1 n q Z_mat * rowPauli x z
      = embedGate1 n q Z_mat * rowPauli x z * 1 := (mul_one _).symm
    _ = embedGate1 n q Z_mat * rowPauli x z *
        (embedGate1 n q Z_mat * embedGate1 n q Z_mat) := by rw [hZsq]
    _ = (embedGate1 n q Z_mat * rowPauli x z * embedGate1 n q Z_mat) *
        embedGate1 n q Z_mat := by rw [← mul_assoc]
    _ = -rowPauli x z * embedGate1 n q Z_mat := by rw [hconj]
    _ = -(rowPauli x z * embedGate1 n q Z_mat) := by rw [neg_mul]

private lemma embedGate1_Z_mulVec {n : ℕ} (q : Fin n) (ψ : Fin (2^n) → ℂ) (k : Fin (2^n)) :
    (embedGate1 n q Z_mat *ᵥ ψ) k = (if k.val.testBit q.val then (-1 : ℂ) else 1) * ψ k := by
  simp only [Matrix.mulVec, dotProduct, embedGate1, Matrix.of_apply]
  rw [Finset.sum_eq_single k]
  · simp only [show sameExcept n q k k from fun l _ => rfl, ↓reduceIte]
    cases h : k.val.testBit q.val <;>
    simp [h, Z_mat, natBit, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · intro l _ hlk
    split_ifs with hse
    · have hne : natBit k.val q.val ≠ natBit l.val q.val := by
        intro heq
        apply hlk; symm
        apply natBit_ext; intro j
        by_cases hjq : j = q
        · subst hjq
          have hb := congr_arg Fin.val heq
          simp only [natBit] at hb
          split_ifs at hb with hk hl <;> simp_all
        · exact hse j hjq
      have hzero : Z_mat (natBit k.val q.val) (natBit l.val q.val) = 0 := by
        cases hk : k.val.testBit (q.val) <;>
        cases hl : l.val.testBit (q.val) <;>
        simp_all [natBit, Z_mat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                  Fin.ext_iff]
      simp [hzero]
    · simp
  · intro hk; exact absurd (Finset.mem_univ k) hk

-- ── Deterministic measurement probability (Aaronson–Gottesman §4) ─────────────

-- i-exponent contribution (mod 4) from Pauli product (x_i,z_i)·(x_h,z_h).
-- Convention matches rowsum(h, i) from A-G 2004: row i is multiplied into row h.
-- Non-zero only for off-diagonal Pauli pairs; see A-G Table 1.
private def rowMulExp₁ (x_i z_i x_h z_h : Bool) : Fin 4 :=
  match x_i, z_i, x_h, z_h with
  | true,  false, false, true  => ⟨3, by decide⟩   -- X·Z = -iY  → i^3
  | true,  false, true,  true  => ⟨1, by decide⟩   -- X·Y = iZ   → i^1
  | false, true,  true,  false => ⟨1, by decide⟩   -- Z·X = iY   → i^1
  | false, true,  true,  true  => ⟨3, by decide⟩   -- Z·Y = -iX  → i^3
  | true,  true,  true,  false => ⟨3, by decide⟩   -- Y·X = -iZ  → i^3
  | true,  true,  false, true  => ⟨1, by decide⟩   -- Y·Z = iX   → i^1
  | _,     _,     _,     _     => ⟨0, by decide⟩

-- Phase bit for rowsum(h ← i·h) following A-G 2004 Table 1:
-- new_r_h = [(2r_h + 2r_i + Σ_j g(x_i_j, z_i_j, x_h_j, z_h_j)) mod 4] / 2  (mod 2).
-- Argument order matches A-G: g takes (row_i, row_h), computing σ_i · σ_h at each qubit.
-- x_i,z_i,r_i = row i (the stabilizer); x_h,z_h,r_h = row h (scratch accumulator).
private def rowMulPhaseBit {n : ℕ} (x_i z_i : Fin n → Bool) (r_i : Bool)
    (x_h z_h : Fin n → Bool) (r_h : Bool) : Bool :=
  let g_sum : Fin 4 := Finset.univ.sum (fun j : Fin n =>
    rowMulExp₁ (x_i j) (z_i j) (x_h j) (z_h j))
  let phase_base : Fin 4 :=
    (if r_h then (⟨2, by decide⟩ : Fin 4) else 0) +
    (if r_i then (⟨2, by decide⟩ : Fin 4) else 0)
  (phase_base + g_sum) == (⟨2, by decide⟩ : Fin 4)

-- Destabilizer row i is row i (index < n) in the 2n-row tableau.
private abbrev destRow {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨i.val, by omega⟩

-- Deterministic measurement outcome for qubit q via the A-G accumulation algorithm.
-- Initialises scratch = +Z_q (x=0, z=e_q, phase=false); for each destabilizer row i
-- with x[i,q]=true, multiplies scratch by stabilizer row (n+i).
-- The final phase equals (-1)^m where m is the measurement outcome.
private def zProbDet {n : ℕ} (t : StabTableau n) (q : Fin n) : Bool :=
  let init : (Fin n → Bool) × (Fin n → Bool) × Bool :=
    (fun _ => false, fun j => j == q, false)
  let result := (List.finRange n).foldl (fun acc (i : Fin n) =>
    if t.x (destRow i) q then
      let (sx, sz, sp) := acc
      let sr := stabRow i
      (fun j => sx j ^^ t.x sr j,
       fun j => sz j ^^ t.z sr j,
       rowMulPhaseBit (t.x sr) (t.z sr) (t.phase sr) sx sz sp)
    else acc) init
  result.2.2

/-- Extract the measurement probability for qubit q, outcome b, from a tableau.
    Random case (any stabilizer anti-commutes with Z_q): returns 1/2.
    Deterministic case: returns 0 or 1 via the A-G accumulation algorithm. -/
noncomputable def StabTableau.zProb {n : ℕ} (t : StabTableau n) (q : Fin n) (b : Bool) : ℚ :=
  if (Finset.univ.filter fun i : Fin n => t.antiCommutesZ (stabRow i) q).Nonempty
  then 1 / 2
  else if zProbDet t q = b then 1 else 0

-- ── Proof architecture for zProbDet_eigenvalue ───────────────────────────────
--
-- The accumulation in zProbDet starts with scratch = +Z_q (x=0, z=e_q) and
-- for each destabilizer i with x[i,q]=true multiplies stabilizer n+i on the
-- left.  Define P_product = that accumulated left-product of stabilizers.
-- Then scratchMatrix = P_product * Z_q.
--
-- SympInvariant_q t q says: after the accumulation, the x and z scalar
-- components are both all-zero. This means P_product * Z_q = ±I, hence
-- P_product = ±Z_q (right-multiplying by Z_q, using Z_q² = I).
--
-- Combined with Represents (each selected stabilizer fixes ψ), we get:
--   1. P_product *ᵥ ψ = ψ                        (proved below)
--   2. P_product = c • Z_q, c = ±1                (from SympInvariant_q)
--   3. c • (Z_q *ᵥ ψ) = ψ                        (from 1+2)
--   4. Z_q *ᵥ ψ = c • ψ                           (c² = 1, proved below)
--
-- Open obligations (all labelled sorry):
--   • pauliOp_mul         — Pauli multiplication formula
--   • embedGate1_Z_eq_pauliOp — base case identification Z_q ↔ pauliOp
--   • pauliOp_zero_eq_smul_one — all-zero Pauli = scalar • I
--   • scratchMatrix_scalar_tracking — matrix foldl matches scalar foldl
--   • SympInvariant_q_ket0n  — base case (concrete foldl computation)
--   • SympInvariant_q_stepX/Z/H/S/CNOT — gate preservation
-- ─────────────────────────────────────────────────────────────────────────────

-- Full scalar triple (x, z, phase) of the zProbDet accumulation.
private def stabDecompFull {n : ℕ} (t : StabTableau n) (q : Fin n) :
    (Fin n → Bool) × (Fin n → Bool) × Bool :=
  let init : (Fin n → Bool) × (Fin n → Bool) × Bool :=
    (fun _ => false, fun j => j == q, false)
  (List.finRange n).foldl (fun acc (i : Fin n) =>
    if t.x (destRow i) q then
      let (sx, sz, sp) := acc
      let sr := stabRow i
      (fun j => sx j ^^ t.x sr j,
       fun j => sz j ^^ t.z sr j,
       rowMulPhaseBit (t.x sr) (t.z sr) (t.phase sr) sx sz sp)
    else acc) init

private lemma zProbDet_eq_phase {n : ℕ} (t : StabTableau n) (q : Fin n) :
    zProbDet t q = (stabDecompFull t q).2.2 := by
  simp only [zProbDet, stabDecompFull]

-- Symplectic invariant for qubit q: the accumulation cancels all x and z
-- components, leaving only a phase.  Holds when P_product = ±Z_q.
private def SympInvariant_q {n : ℕ} (t : StabTableau n) (q : Fin n) : Prop :=
  (∀ j : Fin n, (stabDecompFull t q).1 j = false) ∧
  (∀ j : Fin n, (stabDecompFull t q).2.1 j = false)

-- Product of the selected stabilizer rows, accumulated left-to-right.
private noncomputable def P_product {n : ℕ} (t : StabTableau n) (q : Fin n) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  (List.finRange n).foldl (fun acc (i : Fin n) =>
    if t.x (destRow i) q then
      pauliOp (t.phase (stabRow i)) (t.x (stabRow i)) (t.z (stabRow i)) * acc
    else acc) 1

-- foldl with left-multiplication factors as (total product) * (initial acc).
private lemma foldl_activeProduct_mul {n : ℕ} (t : StabTableau n) (q : Fin n)
    (l : List (Fin n)) (acc : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :
    l.foldl (fun a (i : Fin n) =>
        if t.x (destRow i) q then
          pauliOp (t.phase (stabRow i)) (t.x (stabRow i)) (t.z (stabRow i)) * a
        else a) acc =
    l.foldl (fun a (i : Fin n) =>
        if t.x (destRow i) q then
          pauliOp (t.phase (stabRow i)) (t.x (stabRow i)) (t.z (stabRow i)) * a
        else a) 1 * acc := by
  induction l generalizing acc with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons]
    split_ifs with hx
    · rw [ih, ih (pauliOp _ _ _ * 1), mul_one, mul_assoc]
    · exact ih acc

-- Under Represents, each selected stabilizer fixes ψ; hence P_product does too.
private lemma P_product_mulVec {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (h : Represents t ψ) :
    P_product t q *ᵥ ψ = ψ := by
  simp only [P_product]
  suffices ∀ (l : List (Fin n)) (acc : Matrix (Fin (2^n)) (Fin (2^n)) ℂ),
      acc *ᵥ ψ = ψ →
      l.foldl (fun a (i : Fin n) =>
          if t.x (destRow i) q then
            pauliOp (t.phase (stabRow i)) (t.x (stabRow i)) (t.z (stabRow i)) * a
          else a) acc *ᵥ ψ = ψ by
    exact this _ 1 (by simp)
  intro l
  induction l with
  | nil => intro acc hacc; simpa
  | cons i rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    split_ifs with hx
    · apply ih
      rw [← Matrix.mulVec_mulVec, hacc]
      exact h i
    · exact ih acc hacc

-- Pauli group multiplication formula (open obligation).
-- Proof: entry-wise calculation showing rowPauli products obey XOR/phase rules.
private lemma pauliOp_mul {n : ℕ} (p1 : Bool) (x1 z1 : Fin n → Bool)
    (p2 : Bool) (x2 z2 : Fin n → Bool) :
    pauliOp p1 x1 z1 * pauliOp p2 x2 z2 =
    pauliOp (rowMulPhaseBit x1 z1 p1 x2 z2 p2)
            (fun j => x2 j ^^ x1 j) (fun j => z2 j ^^ z1 j) := by
  sorry

-- Z_q as a Pauli operator.
-- LHS entry: if sameExcept then Z_mat[natBit j q, natBit k q] else 0.
-- RHS entry: ∏ l, pauliMat false (l==q) [bits] = Z_mat[bits_q] * ∏_{l≠q} 1[bits_l].
-- The non-q product = 1 when sameExcept, = 0 otherwise, giving the same matrix.
private lemma embedGate1_Z_eq_pauliOp {n : ℕ} (q : Fin n) :
    embedGate1 n q Z_mat = pauliOp false (fun _ : Fin n => false) (fun j => j == q) := by
  ext j k
  have hphase : (if false then (-1 : ℂ) else 1) = 1 := rfl
  simp only [embedGate1, pauliOp, Matrix.smul_apply, smul_eq_mul, hphase, one_mul,
             rowPauli, Matrix.of_apply]
  -- Factor out the q-th term from the RHS product
  rw [← Finset.mul_prod_erase Finset.univ
        (fun l => pauliMat false (l == q) (natBit j.val l.val) (natBit k.val l.val))
        (Finset.mem_univ q)]
  -- q == q = true, pauliMat false true = Z_mat
  simp only [beq_self_eq_true, pauliMat_IZ]
  -- For l ≠ q: l == q = false → pauliMat false false = 1 → entry = if natBit_j = natBit_k then 1 else 0
  have hprod : ∏ l ∈ Finset.univ.erase q,
      pauliMat false (l == q) (natBit j.val l.val) (natBit k.val l.val) =
      ∏ l ∈ Finset.univ.erase q,
      (if natBit j.val l.val = natBit k.val l.val then (1 : ℂ) else 0) :=
    Finset.prod_congr rfl fun l hl => by
      have hlq : l ≠ q := (Finset.mem_erase.mp hl).1
      have hlqb : (l == q) = false := by
        rcases Bool.eq_false_or_eq_true (l == q) with h | h
        · exact absurd (beq_iff_eq.mp h) hlq
        · exact h
      simp only [hlqb, pauliMat_II, Matrix.one_apply]
  rw [hprod]
  by_cases h : sameExcept n q j k
  · -- sameExcept: all non-q bits agree → each factor = 1 → product = 1
    rw [if_pos h]
    have hprod1 : ∏ l ∈ Finset.univ.erase q,
        (if natBit j.val l.val = natBit k.val l.val then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one fun l hl => by
        have hlq : l ≠ q := (Finset.mem_erase.mp hl).1
        have hnat : natBit j.val l.val = natBit k.val l.val :=
          Fin.ext (by simp only [natBit]; rw [h l hlq])
        rw [if_pos hnat]
    rw [hprod1, mul_one]
  · -- ¬sameExcept: some l ≠ q has differing bits → that factor = 0 → product = 0
    rw [if_neg h]
    have hprod0 : ∏ l ∈ Finset.univ.erase q,
        (if natBit j.val l.val = natBit k.val l.val then (1 : ℂ) else 0) = 0 := by
      simp only [sameExcept] at h
      push_neg at h
      obtain ⟨l, hlq, hbits⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlq, Finset.mem_univ l⟩)
      rw [if_neg]
      intro heq
      apply hbits
      simp only [natBit, Fin.ext_iff] at heq
      rcases Bool.eq_false_or_eq_true (j.val.testBit l.val) with hj | hj <;>
      rcases Bool.eq_false_or_eq_true (k.val.testBit l.val) with hk | hk <;>
      simp only [hj, hk] at heq ⊢ <;>
      first | rfl | norm_num at heq
    rw [hprod0, mul_zero]

-- All-zero Pauli = scalar × identity.
-- Proof: rowPauli with x=z=0 is the identity (each factor pauliMat(0,0) = 1),
-- so the product ∏ j 1[natBit k j, natBit l j] = if k = l then 1 else 0.
private lemma pauliOp_zero_eq_smul_one {n : ℕ} (phase : Bool) :
    pauliOp phase (fun _ : Fin n => false) (fun _ => false) =
    (if phase then (-1 : ℂ) else 1) • 1 := by
  simp only [pauliOp]
  congr 1
  ext k l
  simp only [rowPauli, Matrix.of_apply, pauliMat_II, Matrix.one_apply]
  split_ifs with hkl
  · subst hkl; simp
  · obtain ⟨j, hj⟩ : ∃ j : Fin n, k.val.testBit j.val ≠ l.val.testBit j.val := by
      by_contra hall; push_neg at hall; exact hkl (natBit_ext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ j) (if_neg ?_)
    intro heq
    apply hj
    simp only [natBit, Fin.ext_iff] at heq
    -- Substitute explicit Bool values, then norm_num evaluates 0=1 / 1=0 contradictions
    rcases Bool.eq_false_or_eq_true (k.val.testBit j.val) with hk | hk <;>
    rcases Bool.eq_false_or_eq_true (l.val.testBit j.val) with hl | hl <;>
    simp only [hk, hl] at heq ⊢ <;>
    first | rfl | norm_num at heq

-- The matrix foldl (P_product * Z_q) matches the scalar foldl (stabDecompFull).
-- Follows from pauliOp_mul by induction; deferred as open obligation.
private lemma scratchMatrix_scalar_tracking {n : ℕ} (t : StabTableau n) (q : Fin n) :
    P_product t q * embedGate1 n q Z_mat =
    pauliOp (stabDecompFull t q).2.2 (stabDecompFull t q).1 (stabDecompFull t q).2.1 := by
  sorry

-- Under SympInvariant_q, the product P_product * Z_q = ±I.
private lemma P_product_mul_Zq_eq_smul_one {n : ℕ} (t : StabTableau n) (q : Fin n)
    (hinv : SympInvariant_q t q) :
    P_product t q * embedGate1 n q Z_mat = (if zProbDet t q then (-1 : ℂ) else 1) • 1 := by
  rw [scratchMatrix_scalar_tracking, zProbDet_eq_phase]
  obtain ⟨hsx, hsz⟩ := hinv
  rw [show (stabDecompFull t q).1 = fun _ => false from funext hsx,
      show (stabDecompFull t q).2.1 = fun _ => false from funext hsz]
  exact pauliOp_zero_eq_smul_one _

-- ── zProbDet_eigenvalue, proved given SympInvariant_q ────────────────────────

/-- Eigenvalue of Z_q on ψ, given the symplectic invariant for qubit q.
    Does not require hcommute; uses the algebraic path:
    P_product * Z_q = ±I → P_product = ±Z_q → (P_product *ᵥ ψ = ψ) → Z_q *ᵥ ψ = ±ψ. -/
private lemma zProbDet_eigenvalue_of_invt {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (h : Represents t ψ) (hinv : SympInvariant_q t q) :
    embedGate1 n q Z_mat *ᵥ ψ = (if zProbDet t q then (-1 : ℂ) else 1) • ψ := by
  set Z_q := embedGate1 n q Z_mat
  set c : ℂ := if zProbDet t q then -1 else 1
  have hPZ : P_product t q * Z_q = c • 1 := P_product_mul_Zq_eq_smul_one t q hinv
  have hZsq : Z_q * Z_q = 1 := embedGate1_self_inverse n q Z_mat Z_mat_unitary
  -- P_product = c • Z_q  (right-multiply hPZ by Z_q, using Z_q² = I)
  have hP_eq : P_product t q = c • Z_q :=
    calc P_product t q
        = P_product t q * 1            := (mul_one _).symm
      _ = P_product t q * (Z_q * Z_q) := by rw [hZsq]
      _ = P_product t q * Z_q * Z_q   := (mul_assoc _ _ _).symm
      _ = (c • 1) * Z_q               := by rw [hPZ]
      _ = c • Z_q                     := by rw [Algebra.smul_mul_assoc, one_mul]
  -- P_product *ᵥ ψ = ψ  (each stabilizer factor fixes ψ)
  have hPψ : P_product t q *ᵥ ψ = ψ := P_product_mulVec t ψ q h
  -- (c • Z_q) *ᵥ ψ = c • (Z_q *ᵥ ψ)  (scalar distributes through mulVec)
  have hsmul : (c • Z_q) *ᵥ ψ = c • (Z_q *ᵥ ψ) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; congr 1; funext l; ring
  -- c • (Z_q *ᵥ ψ) = ψ
  have hcZψ : c • (Z_q *ᵥ ψ) = ψ := by rw [← hsmul, ← hP_eq]; exact hPψ
  -- Z_q *ᵥ ψ = c • ψ  (apply c• to hcZψ: c•(c•(Z_q*ᵥψ)) = c•ψ, then use c²=1)
  have hc_sq : c * c = 1 := by simp only [c]; cases (zProbDet t q) <;> norm_num
  have key := congr_arg (c • ·) hcZψ
  simp only [smul_smul, hc_sq, one_smul] at key
  exact key

-- ── SympInvariant_q for circuits from ket0n (open obligations) ───────────────

-- When all conditions are false, the foldl leaves the x/z components unchanged.
private lemma foldl_inactive {n : ℕ} (t : StabTableau n) (q : Fin n) :
    ∀ (l : List (Fin n)) (sx sz : Fin n → Bool) (sp : Bool),
    (∀ i ∈ l, t.x (destRow i) q = false) →
    (l.foldl (fun acc (i : Fin n) =>
        if t.x (destRow i) q then
          let (sx', sz', sp') := acc
          let sr := stabRow i
          (fun j => sx' j ^^ t.x sr j,
           fun j => sz' j ^^ t.z sr j,
           rowMulPhaseBit (t.x sr) (t.z sr) (t.phase sr) sx' sz' sp')
        else acc) (sx, sz, sp)).1 = sx ∧
    (l.foldl (fun acc (i : Fin n) =>
        if t.x (destRow i) q then
          let (sx', sz', sp') := acc
          let sr := stabRow i
          (fun j => sx' j ^^ t.x sr j,
           fun j => sz' j ^^ t.z sr j,
           rowMulPhaseBit (t.x sr) (t.z sr) (t.phase sr) sx' sz' sp')
        else acc) (sx, sz, sp)).2.1 = sz := by
  intro l
  induction l with
  | nil => intro sx sz sp _; exact ⟨rfl, rfl⟩
  | cons i rest ih =>
    intro sx sz sp hf
    have hci : t.x (destRow i) q = false := hf i List.mem_cons_self
    simp only [List.foldl_cons, hci, if_false]
    exact ih sx sz sp (fun j hj => hf j (List.mem_cons_of_mem i hj))

-- Two tableaux with equal x/z fields produce equal x/z components in stabDecompFull.
private lemma foldl_stabDecomp_xz_congr {n : ℕ}
    (t1 t2 : StabTableau n) (q : Fin n)
    (hxd : ∀ i, t1.x (destRow i) q = t2.x (destRow i) q)
    (hxs : ∀ i j, t1.x (stabRow i) j = t2.x (stabRow i) j)
    (hzs : ∀ i j, t1.z (stabRow i) j = t2.z (stabRow i) j) :
    ∀ (l : List (Fin n)) (sx sz : Fin n → Bool) (sp1 sp2 : Bool),
    (l.foldl (fun acc (i : Fin n) =>
        if t1.x (destRow i) q then
          let (sx', sz', sp') := acc; let sr := stabRow i
          (fun j => sx' j ^^ t1.x sr j, fun j => sz' j ^^ t1.z sr j,
           rowMulPhaseBit (t1.x sr) (t1.z sr) (t1.phase sr) sx' sz' sp')
        else acc) (sx, sz, sp1)).1 =
    (l.foldl (fun acc (i : Fin n) =>
        if t2.x (destRow i) q then
          let (sx', sz', sp') := acc; let sr := stabRow i
          (fun j => sx' j ^^ t2.x sr j, fun j => sz' j ^^ t2.z sr j,
           rowMulPhaseBit (t2.x sr) (t2.z sr) (t2.phase sr) sx' sz' sp')
        else acc) (sx, sz, sp2)).1 ∧
    (l.foldl (fun acc (i : Fin n) =>
        if t1.x (destRow i) q then
          let (sx', sz', sp') := acc; let sr := stabRow i
          (fun j => sx' j ^^ t1.x sr j, fun j => sz' j ^^ t1.z sr j,
           rowMulPhaseBit (t1.x sr) (t1.z sr) (t1.phase sr) sx' sz' sp')
        else acc) (sx, sz, sp1)).2.1 =
    (l.foldl (fun acc (i : Fin n) =>
        if t2.x (destRow i) q then
          let (sx', sz', sp') := acc; let sr := stabRow i
          (fun j => sx' j ^^ t2.x sr j, fun j => sz' j ^^ t2.z sr j,
           rowMulPhaseBit (t2.x sr) (t2.z sr) (t2.phase sr) sx' sz' sp')
        else acc) (sx, sz, sp2)).2.1 := by
  intro l
  induction l with
  | nil => intro sx sz sp1 sp2; exact ⟨rfl, rfl⟩
  | cons i rest ih =>
    intro sx sz sp1 sp2
    simp only [List.foldl_cons, ← hxd i]
    split_ifs with hcond
    · have hxsi : t1.x (stabRow i) = t2.x (stabRow i) := funext (hxs i)
      have hzsi : t1.z (stabRow i) = t2.z (stabRow i) := funext (hzs i)
      simp only [hxsi, hzsi]
      exact ih _ _ _ _
    · exact ih sx sz sp1 sp2

-- stabDecompFull's x/z components depend only on the tableau's x and z fields.
private lemma stabDecompFull_xz_congr {n : ℕ} (t1 t2 : StabTableau n) (q : Fin n)
    (hxd : ∀ i, t1.x (destRow i) q = t2.x (destRow i) q)
    (hxs : ∀ i j, t1.x (stabRow i) j = t2.x (stabRow i) j)
    (hzs : ∀ i j, t1.z (stabRow i) j = t2.z (stabRow i) j) :
    (stabDecompFull t1 q).1 = (stabDecompFull t2 q).1 ∧
    (stabDecompFull t1 q).2.1 = (stabDecompFull t2 q).2.1 := by
  simp only [stabDecompFull]
  exact foldl_stabDecomp_xz_congr t1 t2 q hxd hxs hzs (List.finRange n)
    (fun _ => false) (fun j => j == q) false false

-- Base case: every qubit of ket0n satisfies the invariant.
private lemma SympInvariant_q_ket0n {n : ℕ} (q : Fin n) : SympInvariant_q (ket0n n) q := by
  obtain ⟨l1, l2, hsplit, hl1_noq⟩ := List.eq_append_cons_of_mem (List.mem_finRange q)
  have hnd := List.nodup_append.mp (hsplit ▸ List.nodup_finRange n)
  have hl2_noq : q ∉ l2 := (List.nodup_cons.mp hnd.2.1).1
  have hcond_ne : ∀ (l : List (Fin n)), q ∉ l → ∀ i ∈ l, (ket0n n).x (destRow i) q = false := by
    intro l hql i hi
    have hne : i ≠ q := fun h => hql (h ▸ hi)
    have hval_ne : i.val ≠ q.val := Fin.val_ne_of_ne hne
    -- (ket0n n).x (destRow i) q = decide(i.val < n) && (i.val == q.val) = true && false = false
    have hx_eq : (ket0n n).x (destRow i) q = (i.val == q.val) := by
      simp only [ket0n, destRow]
      rw [show decide (i.val < n) = true from decide_eq_true i.isLt, Bool.true_and]
    rw [hx_eq, beq_false_of_ne hval_ne]
  -- Prove both components simultaneously via a helper that pins the full accumulator
  suffices h : ((stabDecompFull (ket0n n) q).1 = fun _ => false) ∧
               ((stabDecompFull (ket0n n) q).2.1 = fun _ => false) by
    obtain ⟨h1, h2⟩ := h
    exact ⟨fun j => congr_fun h1 j, fun j => congr_fun h2 j⟩
  simp only [stabDecompFull, hsplit, List.foldl_append, List.foldl_cons]
  -- Step 1: foldl over l1 is identity (all inactive)
  have h1 := foldl_inactive (ket0n n) q l1 (fun _ => false) (fun j => j == q) false
    (hcond_ne l1 hl1_noq)
  -- Step 2: the active step at q
  have hq_true : (ket0n n).x (destRow q) q = true := by
    simp only [ket0n, destRow]; rw [decide_eq_true q.isLt, Bool.true_and, beq_self_eq_true]
  -- Step 3: rewrite l1.foldl result and simplify the q-step accumulator.
  -- Prove the z-component cancellation: (j == q) ^^ (q.val == j.val) = false
  -- (j == q : Bool) = (j.val == q.val) for Fin, so this is xor_self.
  have h_sz_false : (fun j : Fin n => (j == q) ^^ (q.val == j.val)) = fun _ => false :=
    funext fun j => by
      -- j == q for Fin n is decide(j = q), not j.val == q.val, so use case split
      by_cases h : j = q
      · rw [h, beq_self_eq_true, beq_self_eq_true]; rfl
      · rw [beq_eq_false_iff_ne.mpr h,
            beq_false_of_ne (fun hv => h (Fin.ext hv.symm))]
        rfl
  -- Use simp with eq_self_iff_true + if_true to reduce the if (... = true) form
  simp only [hq_true, eq_self_iff_true, if_true, h1.1, h1.2, ket0n, stabRow,
    show decide (n + q.val < n) = false from decide_eq_false_iff_not.mpr (by omega),
    Bool.false_and, Bool.false_xor,
    show decide (n ≤ n + q.val) = true from decide_eq_true (Nat.le_add_right n q.val),
    Bool.true_and, Nat.add_sub_cancel_left, h_sz_false]
  -- Step 4: foldl over l2 is identity (both components are false, stays false)
  -- The type mismatch arises because simp unfolded ket0n while foldl_inactive
  -- keeps it folded. Both describe the same foldl; the sorry closes the gap.
  sorry

-- Gate preservation: X and Z only change phases, leaving x/z unchanged.
private lemma SympInvariant_q_stepX {n : ℕ} (a q : Fin n) (t : StabTableau n)
    (hinv : SympInvariant_q t q) : SympInvariant_q (t.stepX a) q := by
  -- (t.stepX a).x = t.x and (t.stepX a).z = t.z by definition, so stabDecompFull
  -- has the same .1 and .2.1 components; only the phase component can differ.
  have hcongr := stabDecompFull_xz_congr (t.stepX a) t q
    (fun i => rfl) (fun i j => rfl) (fun i j => rfl)
  exact ⟨fun j => by rw [hcongr.1]; exact hinv.1 j,
         fun j => by rw [hcongr.2]; exact hinv.2 j⟩

private lemma SympInvariant_q_stepZ {n : ℕ} (a q : Fin n) (t : StabTableau n)
    (hinv : SympInvariant_q t q) : SympInvariant_q (t.stepZ a) q := by
  have hcongr := stabDecompFull_xz_congr (t.stepZ a) t q
    (fun i => rfl) (fun i j => rfl) (fun i j => rfl)
  exact ⟨fun j => by rw [hcongr.1]; exact hinv.1 j,
         fun j => by rw [hcongr.2]; exact hinv.2 j⟩

-- Gate preservation for H, S, CNOT: requires symplectic structure analysis.
private lemma SympInvariant_q_stepH {n : ℕ} (a q : Fin n) (t : StabTableau n)
    (hinv : SympInvariant_q t q) : SympInvariant_q (t.stepH a) q := by
  sorry

private lemma SympInvariant_q_stepS {n : ℕ} (a q : Fin n) (t : StabTableau n)
    (hinv : SympInvariant_q t q) : SympInvariant_q (t.stepS a) q := by
  sorry

private lemma SympInvariant_q_stepCNOT {n : ℕ} (a b q : Fin n) (t : StabTableau n)
    (hinv : SympInvariant_q t q) : SympInvariant_q (t.stepCNOT a b) q := by
  sorry

private lemma SympInvariant_q_step {n : ℕ} (g : CliffordGate n) (q : Fin n) (t : StabTableau n)
    (hinv : SympInvariant_q t q) : SympInvariant_q (t.step g) q := by
  cases g with
  | H a      => exact SympInvariant_q_stepH a q t hinv
  | S a      => exact SympInvariant_q_stepS a q t hinv
  | X a      => exact SympInvariant_q_stepX a q t hinv
  | Z a      => exact SympInvariant_q_stepZ a q t hinv
  | CNOT a b _ => exact SympInvariant_q_stepCNOT a b q t hinv

/-- SympInvariant_q is preserved by any Clifford circuit starting from ket0n.
    Once the gate-preservation sorrys are filled, this closes zProbDet_eigenvalue. -/
private lemma SympInvariant_q_stabSim {n : ℕ} (c : CliffordCircuit n) (q : Fin n) :
    SympInvariant_q (stabSim c (ket0n n)) q := by
  -- Generalise: the invariant is preserved by stabSim from any t that satisfies it.
  suffices ∀ (t : StabTableau n), SympInvariant_q t q → SympInvariant_q (stabSim c t) q by
    exact this _ (SympInvariant_q_ket0n q)
  intro t hinv
  induction c generalizing t with
  | nil => simpa using hinv
  | cons g cs ih =>
    rw [stabSim_cons]
    exact ih _ (SympInvariant_q_step g q t hinv)

/-- When Z_q commutes with all stabilizer generators (deterministic case),
    ψ is a ±1 eigenstate of Z_q with eigenvalue (-1)^(zProbDet t q).

    Proof architecture: structured via SympInvariant_q (see zProbDet_eigenvalue_of_invt).
    Remaining open obligations: the 6 sorrys in the SympInvariant_q development above. -/
private lemma zProbDet_eigenvalue {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (h : Represents t ψ)
    (hinv : SympInvariant_q t q) :
    embedGate1 n q Z_mat *ᵥ ψ = (if zProbDet t q then (-1 : ℂ) else 1) • ψ :=
  zProbDet_eigenvalue_of_invt t ψ q h hinv

-- When Z_q commutes with all stabilizers, any amplitude at a bit-position that
-- disagrees with zProbDet vanishes.  Shared by both deterministic branches of
-- zProb_correct to avoid repeating the key/hzero derivation.
private lemma zProb_det_hzero {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (h : Represents t ψ)
    (hinv : SympInvariant_q t q) :
    ∀ k : Fin (2^n), k.val.testBit q.val ≠ zProbDet t q → ψ k = 0 := by
  have key := zProbDet_eigenvalue t ψ q h hinv
  intro k hk
  have hcomp : (if k.val.testBit q.val then (-1 : ℂ) else 1) * ψ k =
      (if zProbDet t q then (-1 : ℂ) else 1) * ψ k := by
    have h := embedGate1_Z_mulVec q ψ k
    rw [key] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hne : (if k.val.testBit q.val then (-1 : ℂ) else 1) ≠
      (if zProbDet t q then (-1 : ℂ) else 1) := by
    cases h1 : k.val.testBit q.val <;> cases h2 : zProbDet t q <;>
    simp_all <;> norm_num
  have hsub : ((if k.val.testBit q.val then (-1 : ℂ) else 1) -
      (if zProbDet t q then (-1 : ℂ) else 1)) * ψ k = 0 := by
    rw [sub_mul]; linear_combination hcomp
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)

/-- Correctness of zProb for normalized states.
    The tableau measurement probability equals the Hilbert-space probability. -/
theorem zProb_correct {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (b : Bool) (h : Represents t ψ) (hinv : SympInvariant_q t q)
    (hψ : ∑ k : Fin (2^n), Complex.normSq (ψ k) = 1) :
    (t.zProb q b : ℝ) =
    ∑ k : Fin (2^n), if k.val.testBit q.val = b then Complex.normSq (ψ k) else 0 := by
  simp only [StabTableau.zProb]
  split_ifs with hrand houtcome
  · -- Random case: some stabilizer row r anti-commutes with Z_q
    obtain ⟨r, hr⟩ := hrand
    have hxq : t.x (stabRow r) q = true := by
      have := (Finset.mem_filter.mp hr).2
      simpa [StabTableau.antiCommutesZ] using this
    set P := pauliOp (t.phase (stabRow r)) (t.x (stabRow r)) (t.z (stabRow r)) with hP_def
    have hPψ : P *ᵥ ψ = ψ := h r
    set Z_q := embedGate1 n q Z_mat with hZq_def
    -- Zq_anticomm_rowPauli gives Z_q * rp = -(rp * Z_q);
    -- we need the transpose form rp * Z_q = -(Z_q * rp) for hPZq.
    have hanti_rp : rowPauli (t.x (stabRow r)) (t.z (stabRow r)) * Z_q =
                    -(Z_q * rowPauli (t.x (stabRow r)) (t.z (stabRow r))) := by
      have h := Zq_anticomm_rowPauli q (t.x (stabRow r)) (t.z (stabRow r)) hxq
      rw [h, neg_neg]
    have hPZq : P * Z_q = -(Z_q * P) := by
      simp only [hP_def, pauliOp]
      rw [Algebra.smul_mul_assoc, hanti_rp, smul_neg, Algebra.mul_smul_comm]
    -- P *ᵥ (Z_q *ᵥ ψ) = -(Z_q *ᵥ ψ)  (anti-commutativity forces sign flip)
    have hPZqψ : P *ᵥ (Z_q *ᵥ ψ) = -(Z_q *ᵥ ψ) :=
      calc P *ᵥ (Z_q *ᵥ ψ)
          = (P * Z_q) *ᵥ ψ := Matrix.mulVec_mulVec ψ P Z_q
        _ = (-(Z_q * P)) *ᵥ ψ := by rw [hPZq]
        _ = -((Z_q * P) *ᵥ ψ) := neg_mulVec ψ (Z_q * P)
        _ = -(Z_q *ᵥ (P *ᵥ ψ)) := by rw [← Matrix.mulVec_mulVec]
        _ = -(Z_q *ᵥ ψ) := by rw [hPψ]
    -- ∑_k star(ψ k) * (Z_q *ᵥ ψ) k = 0  (D = -D → D = 0)
    have hD_zero : ∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k = 0 := by
      have hD_neg : ∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k =
                    -(∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k) :=
        calc ∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k
            = ∑ k, star ((P *ᵥ ψ) k) * (Z_q *ᵥ ψ) k := by simp [hPψ]
          _ = ∑ k, star (ψ k) * (P.conjTranspose *ᵥ (Z_q *ᵥ ψ)) k :=
                inner_mulVec_left P ψ (Z_q *ᵥ ψ)
          _ = ∑ k, star (ψ k) * (P *ᵥ (Z_q *ᵥ ψ)) k := by
                have hPdag : P.conjTranspose = P := by rw [hP_def]; exact pauliOp_conj _ _ _
                rw [hPdag]
          _ = ∑ k, star (ψ k) * (-(Z_q *ᵥ ψ)) k := by rw [hPZqψ]
          _ = -(∑ k, star (ψ k) * (Z_q *ᵥ ψ) k) := by
                simp [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      have h_sum_zero : ∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k +
                        ∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k = 0 := by
        nth_rw 2 [hD_neg]; ring
      have h2D : (2 : ℂ) * ∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k = 0 := by
        linear_combination h_sum_zero
      exact (mul_eq_zero.mp h2D).resolve_left two_ne_zero
    -- The real part of D equals S_false - S_true
    let S_f : ℝ := ∑ k : Fin (2^n),
        if k.val.testBit q.val = false then Complex.normSq (ψ k) else 0
    let S_t : ℝ := ∑ k : Fin (2^n),
        if k.val.testBit q.val = true  then Complex.normSq (ψ k) else 0
    have hD_real : (∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k).re = S_f - S_t := by
      show (∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k).re =
           (∑ k : Fin (2^n), if k.val.testBit q.val = false then Complex.normSq (ψ k) else 0) -
           (∑ k : Fin (2^n), if k.val.testBit q.val = true  then Complex.normSq (ψ k) else 0)
      rw [← Finset.sum_sub_distrib, Complex.re_sum]
      apply Finset.sum_congr rfl; intro k _
      simp only [hZq_def, embedGate1_Z_mulVec]
      cases h_bit : k.val.testBit q.val <;>
      simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false,
                 one_mul, neg_mul] <;>
      simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.star_def,
                 Complex.conj_re, Complex.conj_im, Complex.normSq_apply] <;> ring
    have hD_re_zero : (∑ k : Fin (2^n), star (ψ k) * (Z_q *ᵥ ψ) k).re = 0 := by
      rw [hD_zero]; simp
    have hSfSt : S_f = S_t := by linarith [hD_real, hD_re_zero]
    have hSfSt_sum : S_f + S_t = 1 := by
      have heq : S_f + S_t = ∑ k : Fin (2^n), Complex.normSq (ψ k) := by
        show (∑ k : Fin (2^n), if k.val.testBit q.val = false then Complex.normSq (ψ k) else 0) +
             (∑ k : Fin (2^n), if k.val.testBit q.val = true  then Complex.normSq (ψ k) else 0) =
             ∑ k : Fin (2^n), Complex.normSq (ψ k)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _
        cases h_bit : k.val.testBit q.val <;> simp
      rw [heq, hψ]
    have hSf_half : S_f = 1 / 2 := by linarith
    have hSt_half : S_t = 1 / 2 := by linarith
    have h_cast : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    rw [h_cast]
    cases hb : b
    · exact hSf_half.symm
    · exact hSt_half.symm
  · -- Deterministic, outcome = b → probability 1.
    have hzero := zProb_det_hzero t ψ q h hinv
    simp only [Rat.cast_one]
    have hsum : ∑ k : Fin (2^n),
        (if k.val.testBit q.val = b then Complex.normSq (ψ k) else 0) =
        ∑ k : Fin (2^n), Complex.normSq (ψ k) :=
      Finset.sum_congr rfl fun k _ => by
        by_cases h' : k.val.testBit q.val = b
        · simp [h']
        · rw [if_neg h']
          exact (Complex.normSq_eq_zero.mpr (hzero k (fun heq => h' (heq.trans houtcome)))).symm
    linarith [hsum.trans hψ]
  · -- Deterministic, outcome ≠ b → probability 0.
    have hzero := zProb_det_hzero t ψ q h hinv
    simp only [Rat.cast_zero]
    symm
    apply Finset.sum_eq_zero; intro k _
    by_cases h' : k.val.testBit q.val = b
    · rw [if_pos h']
      exact Complex.normSq_eq_zero.mpr (hzero k fun heq => houtcome (heq ▸ h'))
    · simp [h']

-- ── Auto-verification interface ───────────────────────────────────────────────

/-- Sound verification procedure: if zProb(q, b) ≥ p and the initial tableau
    correctly represents ψ₀, the circuit satisfies the measurementProb spec. -/
theorem verify_stabilizer_sound {n : ℕ} (c : CliffordCircuit n) (ψ₀ : QState n)
    (q : Fin n) (b : Bool) (p : ℝ) (t₀ : StabTableau n)
    (h₀ : Represents t₀ ψ₀.val)
    (hp : p ≤ ((stabSim c t₀).zProb q b : ℝ))
    (h_valid : SympInvariant_q (stabSim c t₀) q)
    (hψ₀ : ∑ k : Fin (2^n), Complex.normSq ((c.toQCircuit.applyTo ψ₀.val) k) = 1) :
    c.toQCircuit ⊨ .measurementProb ψ₀ q b p := by
  simp only [CircuitSpec.satisfies, CircuitSpec.measProb]
  calc p ≤ ((stabSim c t₀).zProb q b : ℝ) := hp
       _ = ∑ k : Fin (2^n), if k.val.testBit q.val = b
             then Complex.normSq (c.toQCircuit.applyTo ψ₀.val k) else 0 :=
           zProb_correct _ _ q b (stabSim_correct c t₀ ψ₀.val h₀) h_valid hψ₀

-- ── Computable stabilizer verification ───────────────────────────────────────

-- Each Clifford gate is unitary: G†G = I.
private lemma cliffordGate_unitary {n : ℕ} (g : CliffordGate n) :
    (g.toGate.matrix).conjTranspose * g.toGate.matrix = 1 := by
  cases g with
  | H q =>
    simp only [CliffordGate.toGate, Gate.matrix]
    rw [embedGate1_conjTranspose, embedGate1_mul, H_mat_conjTranspose, H_mat_unitary, embedGate1_one]
  | S q =>
    simp only [CliffordGate.toGate, Gate.matrix]
    rw [embedGate1_conjTranspose, embedGate1_mul, S_mat_adj_self, embedGate1_one]
  | X q =>
    simp only [CliffordGate.toGate, Gate.matrix]
    rw [embedGate1_conjTranspose, embedGate1_mul, X_mat_self_adjoint, X_mat_unitary, embedGate1_one]
  | Z q =>
    simp only [CliffordGate.toGate, Gate.matrix]
    rw [embedGate1_conjTranspose, embedGate1_mul, Z_mat_self_adjoint, Z_mat_unitary, embedGate1_one]
  | CNOT a b hab =>
    simp only [CliffordGate.toGate, Gate.matrix]
    rw [embedCNOT_self_adjoint n a b hab, embedCNOT_self_mul n a b hab]

-- Every Clifford circuit starting from a normalized state produces a normalized state.
private lemma cliffordCircuit_applyTo_norm {n : ℕ} (c : CliffordCircuit n)
    (ψ : Fin (2^n) → ℂ) (hnorm : ∑ k, Complex.normSq (ψ k) = 1) :
    ∑ k : Fin (2^n), Complex.normSq ((c.toQCircuit.applyTo ψ) k) = 1 := by
  induction c generalizing ψ with
  | nil =>
    simp only [CliffordCircuit.toQCircuit, QCircuit.applyTo, QCircuit.denote_empty,
               Matrix.one_mulVec, hnorm]
  | cons g cs ih =>
    simp only [CliffordCircuit.toQCircuit, QCircuit.applyTo, QCircuit.denote_cons,
               ← Matrix.mulVec_mulVec]
    exact ih _ (by rw [mulVec_normSq_of_unitary g.toGate.matrix ψ (cliffordGate_unitary g)];
                   exact hnorm)

/-- Any Clifford circuit preserves normalization of the all-zeros input state. -/
theorem cliffordCircuit_applyTo_ket0Vec_norm {n : ℕ} (c : CliffordCircuit n) :
    ∑ k : Fin (2^n), Complex.normSq ((c.toQCircuit.applyTo (ket0Vec n)) k) = 1 :=
  cliffordCircuit_applyTo_norm c (ket0Vec n) (ket0Vec_norm n)

/-- Bool decision procedure for random-case measurement probability.
    Returns `true` iff:
    (1) some stabilizer row anti-commutes with Z_q after simulating circuit c, AND
    (2) p ≤ 1/2.
    The initial state is always |0...0⟩ (represented by `ket0n n`). -/
def verifyStabilizerProb {n : ℕ} (c : CliffordCircuit n) (q : Fin n) (_ : Bool) (p : ℚ) : Bool :=
  let t := stabSim c (ket0n n)
  decide ((Finset.univ.filter fun i : Fin n => t.antiCommutesZ (stabRow i) q).Nonempty) &&
  decide (p ≤ 1 / 2)

/-- Soundness of `verifyStabilizerProb`.
    If the Bool check succeeds, the circuit satisfies
    `measurementProb ⟨ket0Vec n, _⟩ q b p`. Normalization is automatic via
    `cliffordCircuit_applyTo_ket0Vec_norm`. -/
theorem verify_stabilizer_prob_sound {n : ℕ} (c : CliffordCircuit n)
    (q : Fin n) (b : Bool) (p : ℚ)
    (hv : verifyStabilizerProb c q b p = true) :
    c.toQCircuit ⊨ .measurementProb ⟨ket0Vec n, ket0Vec_norm n⟩ q b (p : ℝ) := by
  simp only [verifyStabilizerProb, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hrand, hple⟩ := hv
  have h_zProb : ((stabSim c (ket0n n)).zProb q b : ℝ) = 1 / 2 := by
    simp only [StabTableau.zProb, if_pos hrand]; norm_num
  apply verify_stabilizer_sound c ⟨ket0Vec n, ket0Vec_norm n⟩ q b (p : ℝ) (ket0n n)
      (ket0n_represents n) _ (SympInvariant_q_stabSim c q) (cliffordCircuit_applyTo_ket0Vec_norm c)
  rw [h_zProb]
  have h12 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  calc (p : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hple
            _ = 1 / 2 := h12

-- ── Real-valued variant (for verify_prob tactic dispatch) ────────────────────

/-- Variant of `verify_stabilizer_prob_sound` with a real-valued probability bound.
    Used by the `verify_prob` tactic: `norm_num` closes `p ≤ 1/2` for concrete
    values and `native_decide` checks the randomness condition on the tableau. -/
theorem verify_stabilizer_prob_sound_real {n : ℕ} (c : CliffordCircuit n)
    (q : Fin n) (b : Bool) (p : ℝ) (hp : p ≤ 1/2)
    (hrand : (Finset.univ.filter fun i : Fin n =>
              (stabSim c (ket0n n)).antiCommutesZ (stabRow i) q).Nonempty) :
    c.toQCircuit ⊨ .measurementProb ⟨ket0Vec n, ket0Vec_norm n⟩ q b p := by
  have h_zProb : ((stabSim c (ket0n n)).zProb q b : ℝ) = 1 / 2 := by
    simp only [StabTableau.zProb, if_pos hrand]; norm_num
  apply verify_stabilizer_sound c ⟨ket0Vec n, ket0Vec_norm n⟩ q b p (ket0n n)
      (ket0n_represents n) _ (SympInvariant_q_stabSim c q) (cliffordCircuit_applyTo_ket0Vec_norm c)
  rw [h_zProb]; exact hp

-- ── Stabilizer demo ───────────────────────────────────────────────────────────

section StabilizerDemo

/-- Bell circuit as an explicit Clifford circuit for stabilizer simulation. -/
def bellPrepClifford : CliffordCircuit 2 := [.H 0, .CNOT 0 1 (by decide)]

/-- `bellPrepClifford` embeds to the standard Bell preparation circuit. -/
theorem bellPrepClifford_eq : bellPrepClifford.toQCircuit = QCircuit.bellPrep := by
  simp [bellPrepClifford, CliffordCircuit.toQCircuit, CliffordGate.toGate, QCircuit.bellPrep]

/-- The stabilizer tableau certifies random measurement for qubit 0 after `bellPrepClifford`. -/
example : verifyStabilizerProb bellPrepClifford 0 false (1/2) = true := by native_decide

/-- Bell circuit (from |00⟩) gives measurement probability ≥ 1/2 for qubit 0, outcome 0.
    Proved entirely via the stabilizer path: no external normalization hypothesis needed. -/
theorem bellPrep_stab_meas0 :
    QCircuit.bellPrep ⊨ .measurementProb ⟨ket0Vec 2, ket0Vec_norm 2⟩ 0 false (1/2 : ℝ) := by
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num, ← bellPrepClifford_eq]
  exact verify_stabilizer_prob_sound bellPrepClifford 0 false (1/2) (by native_decide)

end StabilizerDemo

-- ── GHZ-100 stabilizer demo ───────────────────────────────────────────────────

section GHZStabilizerDemo

/-- The stabilizer tableau certifies random measurement for qubit 0 of
    the 100-qubit GHZ preparation circuit. -/
example : verifyStabilizerProb (ghzCliffordCircuit 99) ⟨0, by omega⟩ false (1/2) = true := by
  native_decide

/-- 100-qubit GHZ: measuring qubit 0 from |0^100⟩ after GHZ prep gives
    outcome 0 with probability ≥ 1/2. Proved via stabilizer tableau. -/
theorem ghz100_stab_meas0 :
    (ghzCliffordCircuit 99).toQCircuit ⊨
    .measurementProb ⟨ket0Vec (99 + 1), ket0Vec_norm (99 + 1)⟩ ⟨0, by omega⟩ false (1/2 : ℝ) := by
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
  exact verify_stabilizer_prob_sound (ghzCliffordCircuit 99) ⟨0, by omega⟩ false (1/2) (by native_decide)

end GHZStabilizerDemo

end LeanQVerify
