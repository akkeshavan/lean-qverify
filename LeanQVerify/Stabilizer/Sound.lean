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

/-- When Z_q commutes with all stabilizer generators (deterministic case),
    ψ is a ±1 eigenstate of Z_q with eigenvalue (-1)^(zProbDet t q).

    Proof requires Aaronson–Gottesman tableau invariants: the stabilizer rows
    form a maximal abelian subgroup, so their joint +1 eigenspace is
    one-dimensional. Z_q commuting with all generators implies Z_q·ψ lies in
    the same eigenspace, forcing Z_q·ψ = ±ψ; the sign follows from the
    zProbDet accumulation algorithm. These invariants require ~500 lines of
    symplectic linear-algebra infrastructure. -/
private lemma zProbDet_eigenvalue {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (h : Represents t ψ)
    (hcommute : ∀ i : Fin n, t.x (stabRow i) q = false) :
    embedGate1 n q Z_mat *ᵥ ψ = (if zProbDet t q then (-1 : ℂ) else 1) • ψ := by
  sorry

-- When Z_q commutes with all stabilizers, any amplitude at a bit-position that
-- disagrees with zProbDet vanishes.  Shared by both deterministic branches of
-- zProb_correct to avoid repeating the key/hzero derivation.
private lemma zProb_det_hzero {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (h : Represents t ψ)
    (hrand : ¬(Finset.univ.filter fun i : Fin n =>
                t.antiCommutesZ (stabRow i) q).Nonempty) :
    ∀ k : Fin (2^n), k.val.testBit q.val ≠ zProbDet t q → ψ k = 0 := by
  have key := zProbDet_eigenvalue t ψ q h (fun i => by
    by_contra hi
    have hx : t.x (stabRow i) q = true := by
      cases h : t.x (stabRow i) q
      · exact absurd h hi
      · rfl
    exact hrand ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      by simp [StabTableau.antiCommutesZ, hx]⟩⟩)
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
    (q : Fin n) (b : Bool) (h : Represents t ψ)
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
    have hzero := zProb_det_hzero t ψ q h hrand
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
    have hzero := zProb_det_hzero t ψ q h hrand
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
    (hψ₀ : ∑ k : Fin (2^n), Complex.normSq ((c.toQCircuit.applyTo ψ₀.val) k) = 1) :
    c.toQCircuit ⊨ .measurementProb ψ₀ q b p := by
  simp only [CircuitSpec.satisfies, CircuitSpec.measProb]
  calc p ≤ ((stabSim c t₀).zProb q b : ℝ) := hp
       _ = ∑ k : Fin (2^n), if k.val.testBit q.val = b
             then Complex.normSq (c.toQCircuit.applyTo ψ₀.val k) else 0 :=
           zProb_correct _ _ q b (stabSim_correct c t₀ ψ₀.val h₀) hψ₀

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
      (ket0n_represents n) _ (cliffordCircuit_applyTo_ket0Vec_norm c)
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
      (ket0n_represents n) _ (cliffordCircuit_applyTo_ket0Vec_norm c)
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
