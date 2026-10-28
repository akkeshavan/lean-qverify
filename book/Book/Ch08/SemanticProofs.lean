import LeanQVerify.Spec.StandardSpecs
import LeanQVerify.Tactic.VerifyProb
import LeanQVerify.Stabilizer.Sound

/-!
# Chapter 8 — Semantic Proofs

Read `prose.md` in this directory alongside this file.

Semantic proofs reason about what the circuit computes — output
state amplitudes and measurement probabilities.
-/

open LeanQVerify QCircuit CircuitSpec Complex

-- ── 1. The 38 proved theorems include semantic results ────────────────────────

-- These are kernel-checked proofs about output probabilities:
#check @bellPrep_entangled       -- P(qubit 0 = 0 | |00⟩ input) ≥ 1/2
#check @bellPrep_entangled_one   -- P(qubit 0 = 1 | |00⟩ input) ≥ 1/2
#check @bellPrep_joint_ket00     -- P(|00⟩) ≥ 1/2 from |00⟩
#check @bellPrep_joint_ket11     -- P(|11⟩) ≥ 1/2 from |00⟩
#check @bellPrep_joint_ket01_zero -- P(|01⟩) = 0 from |00⟩
#check @bellPrep_joint_ket10_zero -- P(|10⟩) = 0 from |00⟩
#check @groverStep2_correct      -- P(target qubit = 1) ≥ 0.99 after Grover step

-- ── 2. What these theorems mean ───────────────────────────────────────────────

-- bellPrep_joint_ket00 and bellPrep_joint_ket11:
--   The Bell circuit, starting from |00⟩, produces |00⟩ or |11⟩ each with
--   probability ≥ 1/2. Together with prob_sum_one, each is exactly 1/2.

-- bellPrep_joint_ket01_zero says:
--   bellPrep ⊨ .jointMeasProb QState.ket00 ⟨1, _⟩ 0
--   This states "P(|01⟩) ≥ 0" which is vacuously true (probabilities are non-negative).
--   The meaningful content is that bellPrep_applies_to_ket00 establishes the exact
--   amplitude at index 1 is zero. See Ch08/prose.md for the non-vacuous version.

-- bellPrep_entangled: this proves a marginal probability lower bound on qubit 0,
--   not entanglement as a formal property. See Ch08/prose.md for discussion.

-- ── 3. How semantic proofs are structured ─────────────────────────────────────

-- Step 1: prove what state the circuit produces from the input
-- Step 2: compute the relevant probability from that state

-- The library does this via:
--   bellPrep_applies_to_ket00 : bellPrep.applyTo ket00.val = bellOutput
-- where bellOutput is the explicit amplitude vector for the Bell state.

-- Then probability bounds follow by norm_num on the explicit amplitudes.

-- ── 4. Gate algebra: H ∘ H = I ────────────────────────────────────────────────

-- These are circuit-level identities (equivalences between circuits).
#check @H_H_eq_id     -- a two-H circuit ≅ the empty circuit
#check @X_X_eq_id     -- a two-X circuit ≅ the empty circuit
#check @H_X_H_eq_Z    -- H ∘ X ∘ H ≅ Z
#check @H_Z_H_eq_X    -- H ∘ Z ∘ H ≅ X

-- These are proved by matrix computation: unwrap both sides to 2×2 or 4×4
-- complex matrices and check they are equal entry by entry.

-- ── 5. Using proved theorems as building blocks ───────────────────────────────

-- If you know H ∘ H = I and X ∘ X = I, you can conclude things about
-- circuits containing H or X pairs without re-proving from scratch.

-- Directly applying H_H_eq_id from the library:
-- H_H_eq_id takes the number of qubits and the qubit index explicitly.
example : (QCircuit.ofGate (.H (⟨0, by norm_num⟩ : Fin 1)) ++
           QCircuit.ofGate (.H ⟨0, by norm_num⟩)) ≅
          (QCircuit.identity : QCircuit 1) :=
  H_H_eq_id 1 ⟨0, by norm_num⟩

-- ── 6. Automated semantic proofs: verify_prob ─────────────────────────────────

-- The manual approach above is complete but verbose.  The `verify_prob` tactic
-- automates measurement-probability goals for small circuits and for Clifford
-- circuits of any size.  No manual matrix algebra is needed.

-- Bell circuit: P(q₀ = 0) ≥ 1/2, proved in one line.
example : QCircuit.bellPrep ⊨ .measurementProb QState.ket00 0 false (1/2) := by
  verify_prob

-- Bell circuit: joint P(|00⟩) ≥ 1/2.
example : QCircuit.bellPrep ⊨ .jointMeasProb QState.ket00 ⟨0, by decide⟩ (1/2) := by
  verify_prob

-- GHZ 3-qubit: joint P(|000⟩) ≥ 1/2.
example : QCircuit.ghzPrep ⊨ .jointMeasProb QState.ket000 ⟨0, by decide⟩ (1/2) := by
  verify_prob

-- ── 7. Clifford circuits: stabilizer backend ─────────────────────────────────

-- For Clifford circuits expressed as `CliffordCircuit.toQCircuit`, verify_prob
-- dispatches to the stabilizer tableau backend instead of the dense evaluator.
-- The tableau backend runs in O(n²) per gate, handling large qubit counts that
-- are impossible with explicit matrix evaluation.

-- bellPrepClifford is the Bell circuit as a CliffordCircuit.
-- verify_prob detects the CliffordCircuit.toQCircuit form and dispatches to
-- verify_stabilizer_prob_sound_real + native_decide automatically.
example : bellPrepClifford.toQCircuit ⊨
    .measurementProb ⟨ket0Vec 2, ket0Vec_norm 2⟩ 0 false (1/2 : ℝ) := by
  verify_prob

-- 100-qubit GHZ: dense evaluation is impossible (2^100 amplitudes).
-- The stabilizer backend handles it in O(n²) via native_decide.
example : (ghzCliffordCircuit 99).toQCircuit ⊨
    .measurementProb ⟨ket0Vec 100, ket0Vec_norm 100⟩ ⟨0, by omega⟩ false (1/2 : ℝ) := by
  verify_prob
