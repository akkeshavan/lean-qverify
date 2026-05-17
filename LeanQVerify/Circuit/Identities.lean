import LeanQVerify.Circuit.QCircuit

/-!
# Gate Identities

Proved equivalences between circuits.

## Proof status

**All theorems fully proved** (kernel-checked, no sorry):
- `H_H_eq_id`, `X_X_eq_id`, `Z_Z_eq_id`, `Y_Y_eq_id`: self-inverse single-qubit gates
- `CNOT_CNOT_eq_id`: CNOT applied twice is identity
- `H_X_H_eq_Z`, `H_Z_H_eq_X`: Hadamard conjugation identities
- `RZ_zero_eq_id`: Rz(0) is identity
- `RZ_add`: consecutive Rz rotations compose
- `SWAP_eq_three_CNOTs`: SWAP equals three CNOTs via XOR bit-flip identity

The single-qubit proofs reduce to `embedGate1_self_inverse` via `embedGate1_mul`.
`SWAP_eq_three_CNOTs` uses a 4-case bit analysis (`cnot3_FF/FT/TF/TT`) proved
by `Nat.eq_of_testBit_eq`, combined with `Finset.sum_eq_single` to collapse the
permutation-matrix sums.
-/

namespace LeanQVerify

open QCircuit

-- ---------------------------------------------------------------------------
-- H ∘ H = identity
-- ---------------------------------------------------------------------------

/-- Applying Hadamard twice recovers the identity. -/
theorem H_H_eq_id (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.H i)) ≅ QCircuit.id := by
  unfold equiv id ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  exact embedGate1_self_inverse n i H_mat H_mat_unitary

-- ---------------------------------------------------------------------------
-- X ∘ X = identity
-- ---------------------------------------------------------------------------

/-- Pauli X is its own inverse. -/
theorem X_X_eq_id (n : ℕ) (i : Fin n) :
    (ofGate (.X i) ++ ofGate (.X i)) ≅ QCircuit.id := by
  unfold equiv id ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  exact embedGate1_self_inverse n i X_mat X_mat_unitary

-- ---------------------------------------------------------------------------
-- Z ∘ Z = identity
-- ---------------------------------------------------------------------------

/-- Pauli Z is its own inverse. -/
theorem Z_Z_eq_id (n : ℕ) (i : Fin n) :
    (ofGate (.Z i) ++ ofGate (.Z i)) ≅ QCircuit.id := by
  unfold equiv id ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  exact embedGate1_self_inverse n i Z_mat Z_mat_unitary

-- ---------------------------------------------------------------------------
-- Y ∘ Y = identity
-- ---------------------------------------------------------------------------

/-- Pauli Y is its own inverse. -/
theorem Y_Y_eq_id (n : ℕ) (i : Fin n) :
    (ofGate (.Y i) ++ ofGate (.Y i)) ≅ QCircuit.id := by
  unfold equiv id ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  exact embedGate1_self_inverse n i Y_mat Y_mat_unitary

-- ---------------------------------------------------------------------------
-- CNOT ∘ CNOT = identity
-- ---------------------------------------------------------------------------

/-- CNOT applied twice recovers the identity. -/
theorem CNOT_CNOT_eq_id (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    (ofGate (.CNOT c t) ++ ofGate (.CNOT c t)) ≅ QCircuit.id := by
  unfold equiv id ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  exact embedCNOT_self_mul n c t hct

-- ---------------------------------------------------------------------------
-- H X H = Z  (Hadamard conjugates X to Z)
-- ---------------------------------------------------------------------------

/-- The Hadamard gate conjugates X to Z. -/
theorem H_X_H_eq_Z (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.X i) ++ ofGate (.H i)) ≅ ofGate (.Z i) := by
  unfold equiv ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  -- Reduces to: embedGate1 n i H_mat * embedGate1 n i X_mat * embedGate1 n i H_mat
  --           = embedGate1 n i Z_mat
  -- Using embedGate1_mul twice: LHS = embedGate1 n i (H_mat * X_mat * H_mat)
  -- And H_mat * X_mat * H_mat = Z_mat (2×2 identity)
  rw [show embedGate1 n i H_mat * (embedGate1 n i X_mat * embedGate1 n i H_mat) =
        embedGate1 n i (H_mat * X_mat * H_mat) by
    rw [← embedGate1_mul, ← embedGate1_mul, Matrix.mul_assoc]]
  congr 1
  -- H * X * H = Z (2×2 matrix identity)
  ext a b; fin_cases a <;> fin_cases b
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, H_mat, X_mat, Z_mat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val']
  all_goals {
    push_cast
    have hne : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith [hsq]
  }

-- ---------------------------------------------------------------------------
-- H Z H = X
-- ---------------------------------------------------------------------------

/-- The Hadamard gate conjugates Z to X. -/
theorem H_Z_H_eq_X (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.Z i) ++ ofGate (.H i)) ≅ ofGate (.X i) := by
  unfold equiv ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  rw [show embedGate1 n i H_mat * (embedGate1 n i Z_mat * embedGate1 n i H_mat) =
        embedGate1 n i (H_mat * Z_mat * H_mat) by
    rw [← embedGate1_mul, ← embedGate1_mul, Matrix.mul_assoc]]
  congr 1
  ext a b; fin_cases a <;> fin_cases b
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two, H_mat, X_mat, Z_mat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val']
  all_goals {
    push_cast
    have hne : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith [hsq]
  }

-- ---------------------------------------------------------------------------
-- Helper lemmas for SWAP = three CNOTs
-- ---------------------------------------------------------------------------

/-- Bit k of (1 <<< k) is true. -/
private lemma shift_testBit_same (k : ℕ) : (1 <<< k).testBit k = true := by
  simp [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

/-- Bit l of (1 <<< k) is false when l ≠ k. -/
private lemma shift_testBit_ne (k l : ℕ) (h : l ≠ k) : (1 <<< k).testBit l = false := by
  simp [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, h]

/-- bi=F, bj=F: three CNOTs leave a unchanged; SWAP target also equals a. -/
private lemma cnot3_FF (i j : ℕ) (hij : i ≠ j) (a : ℕ)
    (hbi : a.testBit i = false) (hbj : a.testBit j = false) :
    a = Nat.ldiff (Nat.ldiff a (1 <<< i)) (1 <<< j) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_ldiff]
  by_cases hki : k = i
  · subst hki
    simp [shift_testBit_same i, shift_testBit_ne j i hij, hbi]
  · by_cases hkj : k = j
    · subst hkj
      simp [shift_testBit_ne i j hij.symm, shift_testBit_same j, hbj]
    · simp [shift_testBit_ne i k hki, shift_testBit_ne j k hkj]

/-- bi=T, bj=F: three CNOTs produce a^^^(1<<<j)^^^(1<<<i); SWAP target equals that. -/
private lemma cnot3_TF (i j : ℕ) (hij : i ≠ j) (a : ℕ)
    (hbi : a.testBit i = true) (hbj : a.testBit j = false) :
    a ^^^ (1 <<< j) ^^^ (1 <<< i) = Nat.ldiff a (1 <<< i) ||| (1 <<< j) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_xor, Nat.testBit_ldiff, Nat.testBit_or]
  by_cases hki : k = i
  · subst hki
    simp [shift_testBit_same i, shift_testBit_ne j i hij, hbi]
  · by_cases hkj : k = j
    · subst hkj
      simp [shift_testBit_ne i j hij.symm, shift_testBit_same j, hbj]
    · simp [shift_testBit_ne i k hki, shift_testBit_ne j k hkj]

/-- bi=F, bj=T: three CNOTs produce a^^^(1<<<i)^^^(1<<<j); SWAP target equals that. -/
private lemma cnot3_FT (i j : ℕ) (hij : i ≠ j) (a : ℕ)
    (hbi : a.testBit i = false) (hbj : a.testBit j = true) :
    a ^^^ (1 <<< i) ^^^ (1 <<< j) = Nat.ldiff (a ||| (1 <<< i)) (1 <<< j) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_xor, Nat.testBit_ldiff, Nat.testBit_or]
  by_cases hki : k = i
  · subst hki
    simp [shift_testBit_same i, shift_testBit_ne j i hij, hbi]
  · by_cases hkj : k = j
    · subst hkj
      simp [shift_testBit_ne i j hij.symm, shift_testBit_same j, hbj]
    · simp [shift_testBit_ne i k hki, shift_testBit_ne j k hkj]

/-- bi=T, bj=T: three CNOTs cancel back to a; SWAP target also equals a. -/
private lemma cnot3_TT (i j : ℕ) (hij : i ≠ j) (a : ℕ)
    (hbi : a.testBit i = true) (hbj : a.testBit j = true) :
    a = (a ||| (1 <<< i)) ||| (1 <<< j) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_or]
  by_cases hki : k = i
  · subst hki
    simp [shift_testBit_same i, shift_testBit_ne j i hij, hbi]
  · by_cases hkj : k = j
    · subst hkj
      simp [shift_testBit_ne i j hij.symm, shift_testBit_same j, hbj]
    · simp [shift_testBit_ne i k hki, shift_testBit_ne j k hkj]

/-- Core bit identity: CNOT(i,j)∘CNOT(j,i)∘CNOT(i,j) equals SWAP at the nat level. -/
private lemma cnot3_eq_swap_nat (i j : ℕ) (hij : i ≠ j) (a : ℕ) :
    (let a1 := if a.testBit i then a ^^^ (1 <<< j) else a
     let a2 := if a1.testBit j then a1 ^^^ (1 <<< i) else a1
     if a2.testBit i then a2 ^^^ (1 <<< j) else a2)
    = setBit (setBit a i (a.testBit j)) j (a.testBit i) := by
  simp only []
  simp only [setBit]
  cases hbi : a.testBit i <;> cases hbj : a.testBit j <;>
    simp only [hbi, hbj, ite_true, ite_false,
               Nat.testBit_xor,
               shift_testBit_same i, shift_testBit_same j,
               shift_testBit_ne i j hij.symm, shift_testBit_ne j i hij,
               Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.xor_true,
               Bool.not_true, Bool.not_false]
  · exact cnot3_FF i j hij a hbi hbj
  · exact cnot3_FT i j hij a hbi hbj
  · exact cnot3_TF i j hij a hbi hbj
  · simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact cnot3_TT i j hij a hbi hbj

-- ---------------------------------------------------------------------------
-- SWAP = CNOT(c,t) ∘ CNOT(t,c) ∘ CNOT(c,t)
-- ---------------------------------------------------------------------------

/-- SWAP equals three CNOTs. -/
theorem SWAP_eq_three_CNOTs (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    ofGate (.SWAP i j) ≅
    (ofGate (.CNOT i j) ++ ofGate (.CNOT j i) ++ ofGate (.CNOT i j)) := by
  unfold equiv ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  ext a b
  simp only [Matrix.mul_apply, embedSWAP, embedCNOT]
  have hij_val : i.val ≠ j.val := Fin.val_ne_of_ne h
  have hj_lt : 1 <<< j.val < 2 ^ n := by
    simp only [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) j.isLt
  have hi_lt : 1 <<< i.val < 2 ^ n := by
    simp only [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) i.isLt
  -- Abbreviate the outputs of the first two CNOT gates
  set a1v := if a.val.testBit i.val then a.val ^^^ (1 <<< j.val) else a.val
  have ha1_lt : a1v < 2 ^ n := by
    unfold_let a1v; split_ifs
    · exact Nat.xor_lt_two_pow a.isLt hj_lt
    · exact a.isLt
  set a2v := if a1v.testBit j.val then a1v ^^^ (1 <<< i.val) else a1v
  have ha2_lt : a2v < 2 ^ n := by
    unfold_let a2v; split_ifs
    · exact Nat.xor_lt_two_pow ha1_lt hi_lt
    · exact ha1_lt
  -- Bit identity: the three-CNOT output equals the SWAP output
  have hbit : (if a2v.testBit i.val then a2v ^^^ (1 <<< j.val) else a2v) =
              setBit (setBit a.val i.val (a.val.testBit j.val)) j.val (a.val.testBit i.val) :=
    cnot3_eq_swap_nat i.val j.val hij_val a.val
  -- Collapse the nested sums: outer (over x) then inner (over y)
  symm
  rw [Finset.sum_eq_single (⟨a1v, ha1_lt⟩ : Fin (2 ^ n))]
  · -- Unique outer term x = a1v: outer factor is 1
    simp only [Fin.val, if_pos rfl, one_mul]
    rw [Finset.sum_eq_single (⟨a2v, ha2_lt⟩ : Fin (2 ^ n))]
    · -- Unique inner term y = a2v: apply bit identity to close
      simp only [Fin.val, if_pos rfl, one_mul, hbit]
    · intro y _ hy
      simp [show y.val ≠ a2v from fun heq => hy (Fin.ext heq)]
    · simp
  · intro x _ hx
    simp [show x.val ≠ a1v from fun heq => hx (Fin.ext heq)]
  · simp

-- ---------------------------------------------------------------------------
-- Rz(0) = identity
-- ---------------------------------------------------------------------------

/-- Rz with angle 0 is the identity. -/
theorem RZ_zero_eq_id (n : ℕ) (i : Fin n) :
    ofGate (.RZ 0 i) ≅ QCircuit.id := by
  unfold equiv id ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  rw [show embedGate1 n i (Rz_mat 0) = 1 from by
    rw [Rz_zero_id, embedGate1_one]]

-- ---------------------------------------------------------------------------
-- Rz(θ) ∘ Rz(φ) = Rz(θ + φ)
-- ---------------------------------------------------------------------------

/-- Consecutive Rz rotations compose by addition of angles. -/
theorem RZ_add (n : ℕ) (i : Fin n) (θ φ : ℝ) :
    (ofGate (.RZ θ i) ++ ofGate (.RZ φ i)) ≅ ofGate (.RZ (θ + φ) i) := by
  unfold equiv ofGate
  simp only [denote_append, denote, denote_empty, Gate.matrix,
             Matrix.mul_one, Matrix.one_mul]
  rw [embedGate1_mul, Rz_mat_add]

end LeanQVerify
