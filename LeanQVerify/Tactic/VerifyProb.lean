import LeanQVerify.Tactic.EvalCircuit

/-!
# `verify_prob` Tactic

Automated discharge of `measurementProb` and `jointMeasProb` goals for small
circuits (≤ 4 qubits) via gate-by-gate symbolic evaluation.

## How it works

Two-pass strategy that mirrors the manual proofs in `StandardSpecs.lean`:

**Pass 1** — symbolic unfolding (`simp only`, no `decide`):
  Unfolds the spec, circuit structure, gate matrices, and `mulVec`/`dotProduct`
  into explicit row-dot-product expressions without evaluating any matrix entries.

**Pass 2** — concrete evaluation (`simp (decide := true)`):
  Expands finite sums via `Fin.sum_univ_four/two`, evaluates `embedGate1`/
  `embedCNOT` entries (using `decide` for the private `sameExcept` predicate),
  reduces bit operations and arithmetic.

**Pass 3** — residual arithmetic (`norm_num`).

## Limitations (Phase 1)

- Named library circuits (`bellPrep`, `ghzPrep`) are unfolded automatically.
  For user-defined named circuits, precede with `simp only [my_circuit]`.
- Supported gate set: H, X, Y, Z, S, T, CNOT (1–2 qubit circuits).
- `measurementProb` goals require `Fin.sum_univ_four`; works for n = 1 or 2.
- `jointMeasProb` goals (single amplitude) are faster and more reliable.
-/

namespace LeanQVerify

open Matrix Complex QCircuit CircuitSpec

/-- Tactic for discharging measurement probability goals automatically.
    Works for `measurementProb` and `jointMeasProb` on small circuits.

    Named library circuits are unfolded automatically.  For user-defined
    named circuits, precede with `simp only [my_circuit]`. -/
macro "verify_prob" : tactic => `(tactic| (
  -- Pass 1: unfold spec, circuit structure, and mulVec symbolically (no decide)
  simp only [CircuitSpec.satisfies, CircuitSpec.measProb, CircuitSpec.jointMeasProb,
             QCircuit.applyTo, QCircuit.denote, QCircuit.denote_empty,
             -- Named library circuits
             QCircuit.bellPrep, QCircuit.ghzPrep, QCircuit.ofGate,
             -- Gate matrix dispatch
             Gate.matrix,
             -- Matrix arithmetic
             Matrix.mul_one, Matrix.one_mul,
             -- Expand mulVec to row·vector dot products (same order as existing proofs)
             Matrix.mulVec, dotProduct,
             -- Standard input states
             QState.ket0, QState.ket1,
             QState.ket00, QState.ket01, QState.ket10, QState.ket11]
  -- Pass 2: expand sums and evaluate concrete matrix entries.
  -- NOTE: omit `only` so the global @[simp] set is available; this is necessary
  -- for `Fin.sum_univ_four` to fire on `Fin (2^n)` types (which are definitionally
  -- but not syntactically `Fin 4`) — the same strategy used by the hand-written proofs.
  simp (config := { decide := true })
       [Fin.sum_univ_two, Fin.sum_univ_four,
        Matrix.mul_apply,
        LeanQVerify.embedGate1, LeanQVerify.embedCNOT, LeanQVerify.embedCZ,
        LeanQVerify.embedSWAP, LeanQVerify.embedControlled1,
        LeanQVerify.natBit,
        LeanQVerify.H_mat, LeanQVerify.X_mat, LeanQVerify.Y_mat,
        LeanQVerify.Z_mat, LeanQVerify.S_mat, LeanQVerify.T_mat,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const,
        Nat.testBit, Fin.val,
        mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero]
  -- Pass 3: close residual real/complex arithmetic
  try norm_num [Complex.normSq_ofReal, Complex.normSq_inv,
                Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                Real.sqrt_ne_zero'.mpr (show (0:ℝ) < 2 by norm_num)]))

-- ── Demo theorems ─────────────────────────────────────────────────────────────

section Demo

/-- Bell circuit: joint probability of |00⟩ ≥ 1/2, proved automatically. -/
theorem bellPrep_joint_ket00_auto :
    QCircuit.bellPrep ⊨ .jointMeasProb QState.ket00 ⟨0, by decide⟩ (1/2) := by
  verify_prob

/-- Bell circuit: joint probability of |11⟩ ≥ 1/2, proved automatically. -/
theorem bellPrep_joint_ket11_auto :
    QCircuit.bellPrep ⊨ .jointMeasProb QState.ket00 ⟨3, by decide⟩ (1/2) := by
  verify_prob

end Demo

end LeanQVerify
