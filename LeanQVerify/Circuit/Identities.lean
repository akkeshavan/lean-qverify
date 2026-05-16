import LeanQVerify.Circuit.QCircuit

/-!
# Gate Identities

Proved equivalences between circuits.

## Proof status

**Fully proved** (kernel-checked, no sorry):
- `H_H_eq_id`, `X_X_eq_id`, `Z_Z_eq_id`, `Y_Y_eq_id`: self-inverse single-qubit gates
- `CNOT_CNOT_eq_id`: CNOT applied twice is identity
- `H_X_H_eq_Z`, `H_Z_H_eq_X`: Hadamard conjugation identities
- `RZ_zero_eq_id`: Rz(0) is identity
- `RZ_add`: consecutive Rz rotations compose

These proofs reduce to the key lemma `embedGate1_self_inverse`, which uses
`embedGate1_mul`. Both `embedGate1_mul` and its sub-lemma `testBit_sum_factoring`
(the Finset bijection `Fin 2 ≅ {m | sameExcept j m}`) are now proved in
`Unitary.lean` using `Nat.testBit_or/and/not`, `Nat.testBit_two_pow`, and
`Finset.sum_nbij`.

**Still sorry** (one remaining):
- `SWAP_eq_three_CNOTs`: requires a bit-flip XOR composition argument;
  strategy: show setBit(setBit a i bj) j bi = CNOT(i,j)(CNOT(j,i)(CNOT(i,j)(a)))
  using `Nat.testBit_xor` and `Nat.xor_assoc`.
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
  -- Both sides map |a⟩ to the state with bits i and j exchanged.
  -- Direct bit manipulation argument.
  sorry
  -- TODO: Show setBit (setBit a.val i bj) j bi = CNOT(i,j)(CNOT(j,i)(CNOT(i,j)(a)))
  -- Required: Nat.testBit_setBit_same, Nat.testBit_xor, Nat.xor_assoc

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
