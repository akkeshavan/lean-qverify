import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Unitary Matrices and Gate Embeddings

Defines the 2×2 matrices for each standard gate, and the functions that
embed single-qubit and two-qubit gates into the full 2^n × 2^n space.

Key lemmas:
- `H_mat_unitary`, `X_mat_unitary`, `Z_mat_unitary`, `Y_mat_unitary`: 2×2 self-inverse proofs
- `Rz_mat_add`, `Rz_zero_id`: Rz composition identities
- `embedGate1_one`: embedding the identity gives the identity
- `embedGate1_mul`: embedding distributes over matrix multiplication (proved)
- `testBit_sum_factoring`: Fin 2 bijection for the composition sum (proved)
- `embedGate1_self_inverse`: self-inverse 2×2 → self-inverse n-qubit gate
- `embedCNOT_self_mul`: CNOT applied twice is the identity

All theorems in this file are proved without sorry.
-/

namespace LeanQVerify

open Matrix Complex Real

-- ---------------------------------------------------------------------------
-- Bit manipulation helpers
-- ---------------------------------------------------------------------------

/-- Extract bit i of a natural number as a Fin 2. -/
def natBit (j : ℕ) (i : ℕ) : Fin 2 :=
  ⟨if j.testBit i then 1 else 0, by split <;> norm_num⟩

/-- Set bit i of j to value b, returning the new natural number.
    Uses Nat.ldiff to clear bits (avoids Complement Nat). -/
def setBit (j : ℕ) (i : ℕ) (b : Bool) : ℕ :=
  if b then j ||| (1 <<< i) else Nat.ldiff j (1 <<< i)

theorem natBit_lt2 (j i : ℕ) : (natBit j i).val < 2 := (natBit j i).isLt

/-- Two natural numbers less than 2^n are equal iff all their bits 0..n-1 agree. -/
theorem natBit_ext {n : ℕ} {j k : Fin (2^n)}
    (h : ∀ l : Fin n, j.val.testBit l.val = k.val.testBit l.val) : j = k := by
  ext
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < n
  · exact h ⟨p, hp⟩
  · -- bits beyond n-1 are 0 for values < 2^n
    have hpn : n ≤ p := Nat.not_lt.mp hp
    have hjp : j.val < 2^p :=
      j.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) hpn)
    have hkp : k.val < 2^p :=
      k.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) hpn)
    rw [Nat.testBit_eq_false_of_lt hjp, Nat.testBit_eq_false_of_lt hkp]

-- ---------------------------------------------------------------------------
-- Single-qubit gate matrices (2×2 over ℂ)
-- ---------------------------------------------------------------------------

/-- Hadamard gate. -/
noncomputable def H_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := (Real.sqrt 2 : ℝ)⁻¹
  !![s, s; s, -s]

/-- Pauli X (NOT) gate. -/
def X_mat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli Y gate. -/
def Y_mat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli Z gate. -/
def Z_mat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- S gate (phase π/2). -/
def S_mat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, I]

/-- T gate (phase π/4). -/
noncomputable def T_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, exp (I * π / 4)]

/-- Rx(θ) — rotation by θ around X axis. -/
noncomputable def Rx_mat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let c : ℂ := ↑(Real.cos (θ / 2))
  let s : ℂ := ↑(Real.sin (θ / 2))
  !![c, -I * s; -I * s, c]

/-- Ry(θ) — rotation by θ around Y axis. -/
noncomputable def Ry_mat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let c : ℂ := ↑(Real.cos (θ / 2))
  let s : ℂ := ↑(Real.sin (θ / 2))
  !![c, -s; s, c]

/-- Rz(θ) — rotation by θ around Z axis. -/
noncomputable def Rz_mat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![exp (-I * (θ / 2)), 0; 0, exp (I * (θ / 2))]

-- ---------------------------------------------------------------------------
-- 2×2 unitarity proofs
-- ---------------------------------------------------------------------------

theorem X_mat_unitary : X_mat * X_mat = 1 := by
  simp [X_mat, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Z_mat_unitary : Z_mat * Z_mat = 1 := by
  simp [Z_mat, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Y_mat_unitary : Y_mat * Y_mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Y_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.one_apply]
  all_goals ring

/-- H is its own adjoint (real, symmetric). -/
theorem H_mat_conjTranspose : H_mat.conjTranspose = H_mat := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [H_mat, Matrix.conjTranspose, conj_ofReal, Matrix.vecHead,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.transpose_apply]

/-- H * H = I -/
theorem H_mat_unitary : H_mat * H_mat = 1 := by
  have hcne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsqC : ((Real.sqrt 2 : ℝ) : ℂ) * Real.sqrt 2 = 2 :=
    by exact_mod_cast Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [H_mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals push_cast
  all_goals field_simp [hcne, hsqC]

theorem Rz_mat_add (θ φ : ℝ) : Rz_mat θ * Rz_mat φ = Rz_mat (θ + φ) := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Rz_mat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · rw [← Complex.exp_add]; ring_nf
  · rw [← Complex.exp_add]; ring_nf

theorem Rz_zero_id : Rz_mat 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Rz_mat, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  all_goals simp [Complex.exp_zero]

-- ---------------------------------------------------------------------------
-- Embedding single-qubit gates into n-qubit space
-- ---------------------------------------------------------------------------

/-- Condition shorthand: j and k agree on all bits except i. -/
private def sameExcept (n : ℕ) (i : Fin n) (j k : Fin (2^n)) : Prop :=
  ∀ l : Fin n, l ≠ i → j.val.testBit l.val = k.val.testBit l.val

instance instDecidableSameExcept (n : ℕ) (i : Fin n) (j k : Fin (2^n)) :
    Decidable (sameExcept n i j k) :=
  Fintype.decidableForallFintype

/-- Embed a 2×2 gate G acting on qubit i into the 2^n × 2^n space.
    Matrix element (j, k) is G[bit_i(j)][bit_i(k)] if all other bits of j
    and k agree, and 0 otherwise. -/
def embedGate1 (n : ℕ) (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    if sameExcept n i j k
    then G (natBit j.val i.val) (natBit k.val i.val)
    else 0

/-- Embedding the identity matrix gives the identity. -/
theorem embedGate1_one (n : ℕ) (i : Fin n) :
    embedGate1 n i 1 = (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by
  ext j k
  simp only [embedGate1, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [sameExcept, natBit]
  · simp only [hjk, ite_false]
    by_cases hse : sameExcept n i j k
    · simp only [if_pos hse, Matrix.one_apply]
      have hne : natBit j.val i.val ≠ natBit k.val i.val := by
        intro heq
        apply hjk
        apply natBit_ext; intro l
        by_cases hli : l = i
        · rw [hli]
          have hb := congr_arg Fin.val heq
          simp only [natBit] at hb
          by_cases hj : j.val.testBit i.val <;> by_cases hk : k.val.testBit i.val <;>
            simp_all
        · exact hse l hli
      simp [hne]
    · simp [if_neg hse]

/-- Core bit-manipulation lemma needed by embedGate1_mul. -/
private theorem testBit_sum_factoring (n : ℕ) (i : Fin n)
    (j k : Fin (2^n)) (hjk : sameExcept n i j k)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ m : Fin (2^n),
      (if sameExcept n i j m then G (natBit j.val i.val) (natBit m.val i.val) else 0) *
      (if sameExcept n i m k then H (natBit m.val i.val) (natBit k.val i.val) else 0) =
    ∑ b : Fin 2, G (natBit j.val i.val) b * H b (natBit k.val i.val) := by
  -- ① Collapse double condition: given hjk, sameExcept j m → sameExcept m k
  have hmk : ∀ m : Fin (2^n), sameExcept n i j m → sameExcept n i m k :=
    fun m hjm l hl => (hjm l hl).symm.trans (hjk l hl)
  simp_rw [show ∀ m : Fin (2^n),
    (if sameExcept n i j m then G (natBit j.val i.val) (natBit m.val i.val) else 0) *
    (if sameExcept n i m k then H (natBit m.val i.val) (natBit k.val i.val) else 0) =
    if sameExcept n i j m then
      G (natBit j.val i.val) (natBit m.val i.val) * H (natBit m.val i.val) (natBit k.val i.val)
    else 0 from fun m => by
      split_ifs with h₁ h₂ <;> [rfl; exact absurd (hmk m h₁) h₂; simp; simp]]
  -- ② Bit-manipulation sub-lemmas for setBit
  -- 2a. Setting bit p then reading bit p gives b
  have setBit_same : ∀ (v : ℕ) (p : ℕ) (b : Bool),
      (setBit v p b).testBit p = b := by
    intro v p b; unfold setBit; cases b
    · -- b = false: goal has (if false then ... else Nat.ldiff ...).testBit p = false
      show (Nat.ldiff v (1 <<< p)).testBit p = false
      simp [Nat.testBit_ldiff, Nat.shiftLeft_eq, Nat.testBit_two_pow]
    · -- b = true: goal has (if true then v ||| ... else ...).testBit p = true
      show (v ||| (1 <<< p)).testBit p = true
      simp [Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]
  -- 2b. Setting bit p leaves other bits q ≠ p unchanged
  have setBit_ne : ∀ (v : ℕ) (p q : ℕ) (b : Bool), q ≠ p →
      (setBit v p b).testBit q = v.testBit q := by
    intro v p q b hqp; unfold setBit; cases b
    · show (Nat.ldiff v (1 <<< p)).testBit q = v.testBit q
      simp [Nat.testBit_ldiff, Nat.shiftLeft_eq, Nat.testBit_two_pow,
            show p ≠ q from hqp.symm]
    · show (v ||| (1 <<< p)).testBit q = v.testBit q
      simp [Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow,
            show p ≠ q from hqp.symm]
  -- 2c. setBit preserves the < 2^n bound
  have setBit_lt : ∀ (v : ℕ) (p : ℕ) (b : Bool), v < 2^n → p < n → setBit v p b < 2^n := by
    intro v p b hv hp; unfold setBit; cases b
    · -- false: Nat.ldiff v _ ≤ v < 2^n
      show Nat.ldiff v (1 <<< p) < 2^n
      apply Nat.lt_of_le_of_lt _ hv
      apply Nat.le_of_testBit
      intro k hk
      simp only [Nat.testBit_ldiff] at hk
      simp only [Bool.and_eq_true] at hk
      exact hk.1
    · -- true: v ||| (1 <<< p) < 2^n
      apply Nat.or_lt_two_pow hv
      simp only [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by norm_num) hp
  -- ③ Define the bijection mOf : Fin 2 → Fin (2^n)
  let mOf (b : Fin 2) : Fin (2^n) := ⟨setBit j.val i.val (b.val == 1), by
    apply setBit_lt; exact j.isLt; exact i.isLt⟩
  -- mOf b satisfies sameExcept j (mOf b)
  have mOf_same : ∀ b : Fin 2, sameExcept n i j (mOf b) :=
    fun b l hl => (setBit_ne j.val i.val l.val (b.val == 1) (fun h => hl (Fin.ext h))).symm
  -- natBit at position i recovers b
  have mOf_bit : ∀ b : Fin 2, natBit (mOf b).val i.val = b := by
    intro b; apply Fin.ext
    -- (mOf b).val = setBit j.val i.val (b.val == 1), testBit i gives (b.val == 1)
    have step : (mOf b).val.testBit i.val = (b.val == 1) := by
      have h1 : (mOf b).val.testBit i.val =
                (setBit j.val i.val (b.val == 1)).testBit i.val := rfl
      rw [h1, setBit_same]
    simp only [natBit, step]
    fin_cases b <;> simp
  -- Every m with sameExcept j m equals mOf (natBit m i)
  have all_from_mOf : ∀ m : Fin (2^n), sameExcept n i j m → m = mOf (natBit m.val i.val) := by
    intro m hm; apply natBit_ext; intro l
    by_cases hli : l = i
    · rw [hli]
      -- goal: m.val.testBit i.val = (mOf (natBit m.val i.val)).val.testBit i.val
      have h1 : (mOf (natBit m.val i.val)).val.testBit i.val =
                (setBit j.val i.val ((natBit m.val i.val).val == 1)).testBit i.val := rfl
      rw [h1, setBit_same]
      simp only [natBit]
      cases m.val.testBit i.val <;> simp
    · -- l ≠ i: (mOf ...).val.testBit l.val = j.val.testBit l.val = m.val.testBit l.val
      have hval : (mOf (natBit m.val i.val)).val.testBit l.val = j.val.testBit l.val := by
        have h1 : (mOf (natBit m.val i.val)).val.testBit l.val =
                  (setBit j.val i.val ((natBit m.val i.val).val == 1)).testBit l.val := rfl
        rw [h1]
        exact setBit_ne j.val i.val l.val _ (fun h => hli (Fin.ext h))
      rw [hval]
      exact (hm l hli).symm
  -- ④ Reindex: convert sum over Fin(2^n) to a sum over the filter, then over Fin 2
  -- Reindex: convert sum over Fin(2^n) to filter, then bijection to Fin 2
  rw [← Finset.sum_filter]
  apply Finset.sum_bij' (fun m _ => natBit m.val i.val) (fun b _ => mOf b)
  · -- hi: natBit m.val i.val ∈ Finset.univ (trivial)
    intro m _; exact Finset.mem_univ _
  · -- hj: mOf b ∈ filter
    intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mOf_same b⟩
  · -- left_inv: mOf(natBit m.val i.val) = m for m in filter
    intro m hm
    rw [Finset.mem_filter] at hm
    exact (all_from_mOf m hm.2).symm
  · -- right_inv: natBit (mOf b).val i.val = b
    intro b _; exact mOf_bit b
  · -- value agreement: f m = g (natBit m.val i.val) by rfl
    intro m _; rfl

/-- The key composition lemma: embedding distributes over matrix multiplication.
    embedGate1 n i G * embedGate1 n i H = embedGate1 n i (G * H) -/
theorem embedGate1_mul (n : ℕ) (i : Fin n) (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i G * embedGate1 n i H = embedGate1 n i (G * H) := by
  ext j k
  simp only [Matrix.mul_apply, embedGate1]
  split_ifs with hjk
  · -- hjk : ∀ l, l ≠ i → j.val.testBit l.val = k.val.testBit l.val
    exact testBit_sum_factoring n i j k hjk G H
  · apply Finset.sum_eq_zero
    intro m _
    split_ifs with hjm hmk
    · exact absurd (fun l hl => (hjm l hl).trans (hmk l hl)) hjk
    · ring
    · ring
    · ring

-- ---------------------------------------------------------------------------
-- Self-inverse theorems for embedded gates (use embedGate1_mul)
-- ---------------------------------------------------------------------------

/-- Embedding a self-inverse 2×2 gate gives a self-inverse n-qubit gate. -/
theorem embedGate1_self_inverse (n : ℕ) (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : G * G = 1) :
    embedGate1 n i G * embedGate1 n i G = 1 := by
  rw [embedGate1_mul, hG, embedGate1_one]

/-- Embedding the identity gives the identity (needed by embedGate1_mul). -/
theorem embedGate1_one' (n : ℕ) (i : Fin n) :
    embedGate1 n i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := embedGate1_one n i

-- ---------------------------------------------------------------------------
-- Two-qubit gate embeddings
-- ---------------------------------------------------------------------------

/-- CNOT with given control and target qubits.
    Maps |j⟩ to |j XOR (control_bit · 2^target)⟩. -/
def embedCNOT (n : ℕ) (c t : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    let expected : ℕ :=
      if j.val.testBit c.val
      then j.val ^^^ (1 <<< t.val)
      else j.val
    if k.val = expected then 1 else 0

/-- CZ gate: applies a phase flip of −1 when both qubits are |1⟩. -/
def embedCZ (n : ℕ) (c t : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    if j.val ≠ k.val then 0
    else if j.val.testBit c.val && j.val.testBit t.val then -1
    else 1

/-- SWAP gate: exchanges the states of qubits i and j. -/
def embedSWAP (n : ℕ) (i j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun a b =>
    let bi := a.val.testBit i.val
    let bj := a.val.testBit j.val
    let expected := setBit (setBit a.val i.val bj) j.val bi
    if b.val = expected then 1 else 0

/-- Toffoli (CCX) gate: flips target when both controls are |1⟩. -/
def embedCCX (n : ℕ) (c₁ c₂ t : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    let expected : ℕ :=
      if j.val.testBit c₁.val && j.val.testBit c₂.val
      then j.val ^^^ (1 <<< t.val)
      else j.val
    if k.val = expected then 1 else 0

-- ---------------------------------------------------------------------------
-- CNOT self-inverse
-- ---------------------------------------------------------------------------

/-- CNOT applied twice equals the identity (requires control ≠ target). -/
theorem embedCNOT_self_mul (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    embedCNOT n c t * embedCNOT n c t = 1 := by
  ext j k
  simp only [Matrix.mul_apply, embedCNOT, Matrix.one_apply]
  -- bit c of (1 <<< t.val) is 0 since c ≠ t
  have ht_bit : (1 <<< t.val).testBit c.val = false := by
    simp only [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    simp [show t.val ≠ c.val from Fin.val_ne_of_ne (Ne.symm hct)]
  -- XOR with 1<<<t preserves bit c
  have xor_c : ∀ v : ℕ, (v ^^^ 1 <<< t.val).testBit c.val = v.testBit c.val := fun v => by
    rw [Nat.testBit_xor, ht_bit, Bool.xor_false]
  -- 1 <<< t.val < 2^n
  have hshift_lt : 1 <<< t.val < 2^n := by
    simp only [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) t.isLt
  -- XOR preserves < 2^n bound
  have xor_lt : ∀ v : ℕ, v < 2^n → v ^^^ 1 <<< t.val < 2^n := fun v hv =>
    Nat.xor_lt_two_pow hv hshift_lt
  -- CNOT is involutive: cnot(cnot(j)) = j
  have cnot_invol : ∀ v : ℕ, v < 2^n →
      (if (if v.testBit c.val then v ^^^ 1 <<< t.val else v).testBit c.val
       then (if v.testBit c.val then v ^^^ 1 <<< t.val else v) ^^^ 1 <<< t.val
       else (if v.testBit c.val then v ^^^ 1 <<< t.val else v)) = v := by
    intro v _
    cases hb : v.testBit c.val
    · simp [hb]
    · simp only [hb, ite_true, xor_c, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  -- cj = cnot(j), with cj < 2^n
  set cj := if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val with hcj_def
  have hcj : cj < 2^n := by
    simp only [hcj_def]; split_ifs
    · exact xor_lt j.val j.isLt
    · exact j.isLt
  split_ifs with hjk
  · -- k = j: show sum = 1
    subst hjk
    rw [Finset.sum_eq_single ⟨cj, hcj⟩]
    · -- main term: m = ⟨cj, hcj⟩ gives value 1
      have step1 : (⟨cj, hcj⟩ : Fin (2^n)).val =
          (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val) := hcj_def.symm
      simp only [step1, ite_true, one_mul]
      rw [show (if (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val).testBit c.val
               then (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val) ^^^ 1 <<< t.val
               else (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val)) = j.val
           from cnot_invol j.val j.isLt]
      simp
    · -- all other terms are 0
      intro m _ hm_ne
      have h_mval : m.val ≠ cj := fun h => hm_ne (Fin.ext h)
      rw [show (if m.val = (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val)
               then (1:ℂ) else 0) = 0 from by rw [← hcj_def]; exact if_neg h_mval]
      ring
    · simp
  · -- k ≠ j: show sum = 0
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m.val = cj
    · -- m = cnot(j): second factor is 0 since cnot(cj) = j.val ≠ k.val
      have hkj : k.val ≠ j.val := fun h => hjk (Fin.ext h.symm)
      have hm_second : k.val ≠ (if m.val.testBit c.val then m.val ^^^ 1 <<< t.val else m.val) := by
        intro heq; apply hkj
        rw [heq, hm, hcj_def]; exact cnot_invol j.val j.isLt
      rw [show (if m.val = (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val)
               then (1:ℂ) else 0) = 1 from by rw [← hcj_def]; exact if_pos hm,
          show (if k.val = (if m.val.testBit c.val then m.val ^^^ 1 <<< t.val else m.val)
               then (1:ℂ) else 0) = 0 from if_neg hm_second]
      ring
    · -- m ≠ cnot(j): first factor is 0
      rw [show (if m.val = (if j.val.testBit c.val then j.val ^^^ 1 <<< t.val else j.val)
               then (1:ℂ) else 0) = 0 from by rw [← hcj_def]; exact if_neg hm]
      ring

-- ---------------------------------------------------------------------------
-- Previously proved unitarity facts
-- ---------------------------------------------------------------------------

theorem X_mat_self_adjoint : X_mat.conjTranspose = X_mat := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp [Matrix.conjTranspose, X_mat, Matrix.vecHead,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.transpose_apply, star_zero, star_one]

end LeanQVerify
