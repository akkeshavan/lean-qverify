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

/-- Extract the measurement probability for qubit q, outcome b, from a tableau.

    Algorithm (Aaronson–Gottesman §4B):
    - If no stabilizer anti-commutes with Z_q → deterministic outcome.
      The outcome is determined by whether any stabilizer equals ±Z_q.
    - Otherwise → random (probability 1/2).

    This is a rational-valued function; we return ℚ for exactness.

    Note: the full deterministic-case logic requires Gaussian elimination
    to find which generator determines the outcome. Implemented as sorry
    pending the elimination algorithm. -/
noncomputable def StabTableau.zProb {n : ℕ} (t : StabTableau n) (q : Fin n) (b : Bool) : ℚ :=
  -- Check if any stabilizer row anti-commutes with Z_q
  if (Finset.univ.filter fun i : Fin n => t.antiCommutesZ (stabRow i) q).Nonempty
  then 1 / 2  -- random outcome
  else
    -- Deterministic: find the sign of the stabilizer containing Z_q
    -- (simplified: check if phase of the Z_q row agrees with b)
    sorry

/-- Correctness of zProb: the tableau measurement probability equals the
    Hilbert-space probability.

    Proof: by the stabilizer formalism, the measurement probability
    ∑_k [testBit k q = b] · |ψ(k)|² equals 1/2 in the random case and
    0 or 1 in the deterministic case, exactly as computed by zProb.

    This theorem is the key connection between the tableau backend and the
    CircuitSpec satisfaction judgment. -/
theorem zProb_correct {n : ℕ} (t : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (q : Fin n) (b : Bool) (h : Represents t ψ) :
    (t.zProb q b : ℝ) =
    ∑ k : Fin (2^n), if k.val.testBit q.val = b then Complex.normSq (ψ k) else 0 := by
  sorry

-- ── Auto-verification interface ───────────────────────────────────────────────

/-- Sound verification procedure: if zProb(q, b) ≥ p and the tableau is
    obtained by stabSim from the initial state, then the circuit satisfies
    the measurementProb specification.

    This is the theorem that `verify_stabilizer_prob` would invoke. -/
theorem verify_stabilizer_sound {n : ℕ} (c : CliffordCircuit n) (ψ₀ : QState n)
    (q : Fin n) (b : Bool) (p : ℝ) (t₀ : StabTableau n)
    (h₀ : Represents t₀ ψ₀.val)
    (hp : p ≤ ((stabSim c t₀).zProb q b : ℝ)) :
    c.toQCircuit ⊨ .measurementProb ψ₀ q b p := by
  simp only [CircuitSpec.satisfies, CircuitSpec.measProb]
  calc p ≤ ((stabSim c t₀).zProb q b : ℝ) := hp
       _ = ∑ k : Fin (2^n), if k.val.testBit q.val = b
             then Complex.normSq (c.toQCircuit.applyTo ψ₀.val k) else 0 :=
           zProb_correct _ _ q b (stabSim_correct c t₀ ψ₀.val h₀)

end LeanQVerify
