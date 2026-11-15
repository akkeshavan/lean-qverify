import LeanQVerify.ZX.Rules
import LeanQVerify.Circuit.QCircuit

/-!
# Hybrid ZX + Symbolic Rules for Variational Circuits

Bridges the ZX-calculus (Clifford skeleton) with symbolic angle arithmetic
(rotation gates), giving the core identities needed for variational circuit
reasoning.

## Design

The hybrid approach splits variational circuits into two parts:
1. **Clifford skeleton** (H, CNOT, S): rewritten via ZX rules.
2. **Rotation angles** (RZ, RX, RY with symbolic θ : ℝ): handled by
   `ring`, `exp_add`, and Mathlib trig identities.

The bridge between the two parts is the **phase-spider relationship**:
`Rz_mat θ = exp(-I·θ/2) • zSpiderMat 1 1 θ`

Composing this with the ZX color-change rule `H Z(α) H = X(α)` immediately
gives `H_Rz_H_eq_Rx`: the fundamental identity linking Rz and Rx rotations.

## Proof order (no forward references)

1. `zSpiderMat_phase_Rz` — phase bridge (independent, proved by exp_add)
2. `H_zSpider_H_eq_xSpider` — color change (follows from xSpiderMat definition)
3. `xSpiderMat_phase_Rx` — X-phase bridge (proved directly by Euler's formula)
4. `H_Rz_H_eq_Rx` — core hybrid theorem (uses 1, 2, 3)
5. `H_RZ_H_eq_RX_circuit` — circuit-level lift (uses 4 + embedGate1_mul)

## Euler identities used

For `θ : ℝ`:
- `cos(θ/2) = (e^{iθ/2} + e^{-iθ/2}) / 2`   (from `Complex.cos`)
- `-i·sin(θ/2) = (e^{-iθ/2} - e^{iθ/2}) / 2`  (from `Complex.sin`)
-/

namespace LeanQVerify

open Matrix Complex Real QCircuit ZX

-- ============================================================
-- Step 1: Phase bridge Rz_mat ↔ zSpiderMat
-- ============================================================

/-- **Phase bridge**: `exp(-I·θ/2) • zSpiderMat 1 1 θ = Rz_mat θ`.

    The 1×1 Z-spider matrix has entries `[[1, 0], [0, exp(Iθ)]]`.
    Scaling by `exp(-Iθ/2)` gives `[[exp(-Iθ/2), 0], [0, exp(Iθ/2)]] = Rz_mat θ`. -/
theorem zSpiderMat_phase_Rz (θ : ℝ) :
    Complex.exp (-Complex.I * ↑θ / 2) • zSpiderMat 1 1 θ = Rz_mat θ := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.smul_apply, smul_eq_mul, zSpiderMat, Matrix.of_apply,
    Rz_mat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Nat.pow_succ, Nat.pow_zero, Nat.sub_self]
  all_goals norm_num
  -- (0,0): exp(-Iθ/2) * 1 = exp(-I * (θ/2))
  · ring
  -- (1,1): exp(-Iθ/2) * exp(I*θ) = exp(I * (θ/2))  via exp_add
  · rw [← Complex.exp_add]
    push_cast; ring_nf

-- ============================================================
-- Step 2: H conjugation H * zSpider * H = xSpider
-- ============================================================

/-- `H_mat * zSpiderMat 1 1 θ * H_mat = xSpiderMat 1 1 θ`.
    Immediate from the definition `xSpiderMat m n α := hadN n * zSpiderMat m n α * hadN m`
    and `hadN_one : hadN 1 = H_mat`. -/
theorem H_zSpider_H_eq_xSpider (θ : ℝ) :
    H_mat * zSpiderMat 1 1 θ * H_mat = xSpiderMat 1 1 θ := by
  simp only [xSpiderMat, hadN_one]

-- ============================================================
-- Step 3: Core hybrid theorem H * Rz(θ) * H = Rx(θ)  (direct proof)
-- ============================================================

/-- **Core hybrid identity**: `H_mat * Rz_mat θ * H_mat = Rx_mat θ`.

    Proved directly entry-by-entry via Euler's formula:
    - `exp(∓iθ/2) = cos(θ/2) ∓ i·sin(θ/2)`
    - each of the four entries reduces to `cos(θ/2)` or `-i·sin(θ/2)`
      after substituting and using `(1/√2)² = 1/2`. -/
theorem H_Rz_H_eq_Rx (θ : ℝ) : H_mat * Rz_mat θ * H_mat = Rx_mat θ := by
  have hs2 : ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  -- hexp_m/hexp_p match Rz_mat's elaborated form: Lean coerces θ:ℝ to ↑θ:ℂ first,
  -- giving exp(-I * (↑θ / 2)), not exp(-I * ↑(θ/2)).
  have hexp_m : Complex.exp (-Complex.I * (↑θ / 2)) =
      ↑(Real.cos (θ / 2)) - Complex.I * ↑(Real.sin (θ / 2)) := by
    rw [show -Complex.I * (↑θ / 2 : ℂ) = ↑(-(θ / 2)) * Complex.I from by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hexp_p : Complex.exp (Complex.I * (↑θ / 2)) =
      ↑(Real.cos (θ / 2)) + Complex.I * ↑(Real.sin (θ / 2)) := by
    rw [show Complex.I * (↑θ / 2 : ℂ) = ↑(θ / 2) * Complex.I from by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  -- H_mat and Rx_mat have `let` bindings that block cons_val_zero/one from firing after
  -- fin_cases introduces ⟨k, h⟩ indices. Normalize them explicitly.
  have hfin0 : ∀ h : 0 < 2, (⟨0, h⟩ : Fin 2) = 0 := fun _ => Fin.ext rfl
  have hfin1 : ∀ h : 1 < 2, (⟨1, h⟩ : Fin 2) = 1 := fun _ => Fin.ext rfl
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two,
                       H_mat, Rz_mat, Rx_mat, Matrix.of_apply,
                       Matrix.cons_val_zero, Matrix.cons_val_one,
                       mul_zero, add_zero, zero_add,
                       hfin0, hfin1]
  all_goals rw [hexp_m, hexp_p]
  · calc _ = 2 * ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 * ↑(Real.cos (θ / 2)) := by ring
         _ = 2 * (1 / 2 : ℂ) * ↑(Real.cos (θ / 2)) := by rw [hs2]
         _ = ↑(Real.cos (θ / 2)) := by ring
  · calc _ = -(2 * ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 * Complex.I * ↑(Real.sin (θ / 2))) := by ring
         _ = -(2 * (1 / 2 : ℂ) * Complex.I * ↑(Real.sin (θ / 2))) := by rw [hs2]
         _ = -Complex.I * ↑(Real.sin (θ / 2)) := by ring
  · calc _ = -(2 * ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 * Complex.I * ↑(Real.sin (θ / 2))) := by ring
         _ = -(2 * (1 / 2 : ℂ) * Complex.I * ↑(Real.sin (θ / 2))) := by rw [hs2]
         _ = -Complex.I * ↑(Real.sin (θ / 2)) := by ring
  · calc _ = 2 * ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 * ↑(Real.cos (θ / 2)) := by ring
         _ = 2 * (1 / 2 : ℂ) * ↑(Real.cos (θ / 2)) := by rw [hs2]
         _ = ↑(Real.cos (θ / 2)) := by ring

-- ============================================================
-- Step 4: X-phase bridge  exp(-Iθ/2) • xSpider = Rx_mat
-- ============================================================

/-- **X-phase bridge**: `exp(-I·θ/2) • xSpiderMat 1 1 θ = Rx_mat θ`.

    Follows from `H_Rz_H_eq_Rx` via the phase bridge:
    `exp(-Iθ/2) • xSpider = exp(-Iθ/2) • (H·zSpider·H) = H·(exp(-Iθ/2)·zSpider)·H
      = H·Rz·H = Rx`. -/
theorem xSpiderMat_phase_Rx (θ : ℝ) :
    Complex.exp (-Complex.I * ↑θ / 2) • xSpiderMat 1 1 θ = Rx_mat θ := by
  rw [← H_zSpider_H_eq_xSpider]
  rw [show Complex.exp (-Complex.I * ↑θ / 2) • (H_mat * zSpiderMat 1 1 θ * H_mat) =
          H_mat * (Complex.exp (-Complex.I * ↑θ / 2) • zSpiderMat 1 1 θ) * H_mat from by
    simp [smul_mul_assoc, Matrix.mul_smul]]
  rw [zSpiderMat_phase_Rz]
  exact H_Rz_H_eq_Rx θ

-- ============================================================
-- Step 5: Circuit-level lift via embedGate1_mul
-- ============================================================

/-- **Circuit-level identity**: the three-gate sequence `H_i; RZ(θ,i); H_i`
    is equivalent to `RX(θ,i)` on any n-qubit system.

    Uses `embedGate1_mul` to lift the 2×2 identity to the full 2^n space. -/
theorem H_RZ_H_eq_RX_circuit (n : ℕ) (i : Fin n) (θ : ℝ) :
    (ofGate (.H i) ++ ofGate (.RZ θ i) ++ ofGate (.H i)).denote =
    (ofGate (.RX θ i)).denote := by
  simp only [denote_seq, ofGate, denote_cons, denote_empty, mul_one, one_mul, Gate.matrix]
  -- Goal: embedGate1 H * (embedGate1 RZ * embedGate1 H) = embedGate1 RX
  -- Step 1: reassociate so H and RZ are adjacent
  rw [← mul_assoc]
  -- Step 2: fuse H * RZ → embedGate1(H * RZ)
  rw [embedGate1_mul n i H_mat (Rz_mat θ)]
  -- Step 3: fuse (H * RZ) * H → embedGate1((H * RZ) * H)
  rw [embedGate1_mul n i (H_mat * Rz_mat θ) H_mat]
  -- Step 4: apply H * Rz * H = Rx
  rw [H_Rz_H_eq_Rx θ]

/-- Reverse direction: `RX(θ,i)` decomposes as `H_i; RZ(θ,i); H_i`. -/
theorem RX_eq_H_RZ_H_circuit (n : ℕ) (i : Fin n) (θ : ℝ) :
    (ofGate (.RX θ i)).denote =
    (ofGate (.H i) ++ ofGate (.RZ θ i) ++ ofGate (.H i)).denote :=
  (H_RZ_H_eq_RX_circuit n i θ).symm

end LeanQVerify
