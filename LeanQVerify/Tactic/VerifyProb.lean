import LeanQVerify.Tactic.EvalCircuit
import LeanQVerify.Spec.StandardSpecs

/-!
# `verify_prob` Tactic

Automated discharge of `measurementProb` and `jointMeasProb` goals for small
circuits (≤ 4 qubits) via gate-by-gate symbolic evaluation.

## How it works

Three-pass strategy using `evalCircuit` for gate-by-gate evaluation:

**Pass 1** — circuit unfolding via `evalCircuit` (`simp only`, no `decide`):
  Rewrites `c.applyTo ψ → evalCircuit c ψ`, then unfolds the evaluator
  gate by gate using `evalCircuit_cons`, `evalCircuit_empty`, and
  `evalCircuit_append` (for `++` compositions).  After Pass 1, the goal
  contains nested `g.matrix *ᵥ (... *ᵥ ψ)` — one `mulVec` per gate.

**Pass 2** — concrete `mulVec` evaluation (`simp (decide := true)`):
  Evaluates each `g.matrix *ᵥ concrete_state` from the inside out.
  `Fin.sum_univ_four/two/eight` expands the finite dot-product sums;
  `decide := true` evaluates `sameExcept` for `embedGate1`/`embedCNOT`/`embedCZ`.
  Total work is O(n_gates × 4²) rather than O(4^n_gates) from matrix products.

**Pass 3** — residual arithmetic (`norm_num`).

## Key advantage over naive `denote *ᵥ ψ` approach

Using `evalCircuit` avoids building the full matrix product chain
`M_n * … * M_1`.  `Matrix.mul_apply` on an n-gate chain creates O(4^n) nested
sum terms even after zero-elimination.  The `evalCircuit` approach applies each
gate to the current concrete state vector, keeping the term size linear in
the number of gates.

## Limitations (Phase 1)

- Named library circuits (`bellPrep`, `ghzPrep`) are unfolded automatically.
  For user-defined named circuits, precede with `simp only [my_circuit]`.
- Supported gate set: H, X, Y, Z, S, T, CNOT, CZ, SWAP (1–3 qubit circuits).
- For `++` circuits, user must pre-expand named circuit definitions first.
-/

namespace LeanQVerify

open Matrix Complex QCircuit CircuitSpec

-- (1/√2)² = 1/2 in ℂ.  H_mat entries are ↑(√2⁻¹ : ℝ), which the @[simp]
-- lemma Complex.ofReal_inv normalises to (↑√2 : ℂ)⁻¹ before this fires.
-- Must be non-private so `verify_prob` macros called from other files can
-- reference it in their simp lists.
-- Proof strategy:
--  1. `step` (by norm_cast) unifies ((√2:ℂ))⁻¹ to ↑(√2⁻¹ : ℝ).
--  2. ← Complex.ofReal_mul combines ↑a*↑b to ↑(a*b).
--  3. `key` (proved in ℝ via mul_inv_rev + norm_num) rewrites the ℝ product to 1/2.
--  4. simp closes the resulting ↑(1/2 : ℝ) = 1/2 : ℂ.
theorem sqrt2_inv_mul_self :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have key : (Real.sqrt 2 : ℝ)⁻¹ * (Real.sqrt 2 : ℝ)⁻¹ = 1 / 2 := by
    rw [← _root_.mul_inv_rev, hmul]; norm_num
  have step : ((Real.sqrt 2 : ℂ))⁻¹ = ↑((Real.sqrt 2 : ℝ)⁻¹) := by norm_cast
  rw [step, ← Complex.ofReal_mul, key]
  simp

theorem sqrt2_inv_mul_mul (x : ℂ) :
    ((Real.sqrt 2 : ℂ))⁻¹ * (((Real.sqrt 2 : ℂ))⁻¹ * x) = 1 / 2 * x := by
  rw [← mul_assoc, sqrt2_inv_mul_self]

/-- Tactic for discharging measurement probability goals automatically.
    Works for `measurementProb` and `jointMeasProb` on small circuits.

    Named library circuits are unfolded automatically.  For user-defined
    named circuits, precede with `simp only [my_circuit]`. -/
macro "verify_prob" : tactic => `(tactic| (
  -- Pass 1: switch from `applyTo` to `evalCircuit` and unfold gate-by-gate.
  -- Using evalCircuit avoids building the full 2^n × 2^n matrix product chain;
  -- instead each gate is applied to the current state vector individually,
  -- keeping intermediate terms as concrete vectors after Pass 2.
  simp only [CircuitSpec.satisfies, CircuitSpec.measProb, CircuitSpec.jointMeasProb,
             -- Rewrite applyTo → evalCircuit (avoids matrix product explosion)
             LeanQVerify.applyTo_eq_evalCircuit,
             -- Unfold evalCircuit gate by gate (++ handled via evalCircuit_append)
             LeanQVerify.evalCircuit_cons,
             LeanQVerify.evalCircuit_empty,
             LeanQVerify.evalCircuit_append,
             -- Named library circuits (unfold to cons/++ form, then evalCircuit handles it)
             QCircuit.bellPrep, QCircuit.ghzPrep, QCircuit.ofGate,
             -- Gate matrix dispatch
             Gate.matrix,
             -- Standard input states
             QState.ket0, QState.ket1,
             QState.ket00, QState.ket01, QState.ket10, QState.ket11,
             QState.ket000]
  -- Pass 2: expand mulVec and gate matrix entries concretely.
  -- After Pass 1, the goal has nested `M *ᵥ (M *ᵥ (... *ᵥ ket))` for each gate.
  -- simp evaluates the innermost mulVec first (bottom-up), producing a concrete
  -- intermediate state vector after each gate.  This is O(n_gates × 4²) total work
  -- rather than the O(4^n_gates) of expanding the full matrix product.
  -- NOTE: omit `only` so the global @[simp] set normalizes Fin (2^n) types.
  simp (config := { decide := true })
       [Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_eight,
        Matrix.mulVec, dotProduct,
        LeanQVerify.embedGate1, LeanQVerify.embedCNOT, LeanQVerify.embedCZ,
        LeanQVerify.embedSWAP, LeanQVerify.embedControlled1,
        LeanQVerify.natBit,
        LeanQVerify.H_mat, LeanQVerify.X_mat, LeanQVerify.Y_mat,
        LeanQVerify.Z_mat, LeanQVerify.S_mat, LeanQVerify.T_mat,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const,
        Nat.testBit, Fin.val,
        mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero,
        -- Eagerly reduce (1/√2)*(1/√2) = 1/2 and (1/√2)*((1/√2)*x) = 1/2*x.
        -- H_mat entries are ↑(√2⁻¹:ℝ); @[simp] Complex.ofReal_inv normalises
        -- them to (↑√2:ℂ)⁻¹ first, then these lemmas fire.
        LeanQVerify.sqrt2_inv_mul_self,
        LeanQVerify.sqrt2_inv_mul_mul,
        mul_add, add_mul]
  -- Pass 3: close residual complex/real arithmetic.
  -- Strategy: expand normSq to re²+im², push through all complex operations,
  -- then close the resulting ℝ goal with norm_num.
  -- Also try the direct normSq-product path (works when arguments are products).
  try (simp only [Complex.normSq_apply,
                  Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
                  Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
                  Complex.ofReal_re, Complex.ofReal_im,
                  mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, neg_zero]
       norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                 Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                 Real.sqrt_ne_zero'.mpr (show (0:ℝ) < 2 by norm_num)])
  try (simp [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_zero,
             Complex.normSq_one, map_pow, Complex.normSq_ofReal, Complex.normSq_inv]
       norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                 Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)])))

-- ── Demo theorems ─────────────────────────────────────────────────────────────

section Demo

-- ── Bell circuit — jointMeasProb ──────────────────────────────────────────────

/-- Bell circuit: joint probability of |00⟩ ≥ 1/2, proved automatically. -/
theorem bellPrep_joint_ket00_auto :
    QCircuit.bellPrep ⊨ .jointMeasProb QState.ket00 ⟨0, by decide⟩ (1/2) := by
  verify_prob

/-- Bell circuit: joint probability of |11⟩ ≥ 1/2, proved automatically. -/
theorem bellPrep_joint_ket11_auto :
    QCircuit.bellPrep ⊨ .jointMeasProb QState.ket00 ⟨3, by decide⟩ (1/2) := by
  verify_prob

-- ── Bell circuit — measProb (single-qubit marginal) ───────────────────────────

/-- Bell circuit: measuring qubit 0 gives 0 with probability ≥ 1/2. -/
theorem bellPrep_meas_q0_false_auto :
    QCircuit.bellPrep ⊨ .measurementProb QState.ket00 0 false (1/2) := by
  verify_prob

/-- Bell circuit: measuring qubit 0 gives 1 with probability ≥ 1/2. -/
theorem bellPrep_meas_q0_true_auto :
    QCircuit.bellPrep ⊨ .measurementProb QState.ket00 0 true (1/2) := by
  verify_prob

-- ── GHZ circuit — jointMeasProb (3-qubit, Fin 8 sums) ────────────────────────

/-- GHZ circuit: joint probability of |000⟩ ≥ 1/2. -/
theorem ghzPrep_joint_ket000_auto :
    QCircuit.ghzPrep ⊨ .jointMeasProb QState.ket000 ⟨0, by decide⟩ (1/2) := by
  verify_prob

/-- GHZ circuit: joint probability of |111⟩ ≥ 1/2. -/
theorem ghzPrep_joint_ket111_auto :
    QCircuit.ghzPrep ⊨ .jointMeasProb QState.ket000 ⟨7, by decide⟩ (1/2) := by
  verify_prob

-- ── Grover 2-qubit — measurementProb ─────────────────────────────────────────

/-- Grover 2-qubit (1 iteration): measuring qubit 0 gives 1 with probability ≥ 0.99.
    Proved by verify_prob after manually unfolding the named circuit definitions,
    since groverStep2/groverOracle2/groverDiffusion2 are not in Pass 1's simp set. -/
theorem groverStep2_correct_auto :
    (QCircuit.ofGate (.H 0) ++ QCircuit.ofGate (.H 1) ++ groverStep2)
    ⊨ .measurementProb QState.ket00 0 true 0.99 := by
  simp only [groverStep2, groverOracle2, groverDiffusion2]
  verify_prob

end Demo

end LeanQVerify
