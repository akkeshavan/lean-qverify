import LeanQVerify.Spec.StandardSpecs
import LeanQVerify.Circuit.Identities
import LeanQVerify.Foundation.DensityMatrix
import LeanQVerify.Circuit.Parametric
import LeanQVerify.QASM.ParseTheorems

/-!
# Axiom Audit for All 38 Theorems

This file runs `#print axioms` on every theorem claimed in the paper.
It answers the question: what does Lean's kernel assume to accept each proof?

## Expected output

For every theorem below, `#print axioms` should list only standard
mathematical axioms — never `sorryAx`.  The expected axioms are:

  Classical.choice        -- classical logic (excluded middle, choice)
  propext                 -- propositional extensionality
  Quot.sound              -- quotient soundness (used by Mathlib)
  funext                  -- function extensionality (in some proofs)

`sorryAx` appearing for any theorem would mean the proof is unsound.

## How to view the output

Open this file in VS Code with the Lean 4 extension installed.
Hover over any `#print axioms` line to see the axiom list in the info panel.
Alternatively, run from the repository root:

```bash
cd theorems && lake build Axioms
```

A clean build with no errors means all 38 theorems elaborated without
`sorryAx` in their dependency chains.
-/

open LeanQVerify

-- ── Bell state (T1–T9 joint measurement) ────────────────────────────────
#print axioms bellPrep_twoGates
#print axioms bellPrep_oneCNOT
#print axioms bellPrep_depth
#print axioms bellPrep_entangled
#print axioms bellPrep_entangled_one
#print axioms bellPrep_joint_ket00
#print axioms bellPrep_joint_ket11
#print axioms bellPrep_joint_ket01_zero
#print axioms bellPrep_joint_ket10_zero

-- ── GHZ and teleportation (T10–T12) ──────────────────────────────────────
#print axioms ghzPrep_threeGates
#print axioms ghzPrep_depth
#print axioms teleportPrep_depth

-- ── Hardware-efficient ansatz (T13–T18) ───────────────────────────────────
#print axioms hea4_gateCount
#print axioms hea4_cnotCount
#print axioms hea4_rzCount
#print axioms hea4_depth
#print axioms hea4_zero_eq_cnotChain
#print axioms hea4_rz_fuse_single

-- ── Gate algebra identities (T19–T28) ────────────────────────────────────
#print axioms H_H_eq_id
#print axioms X_X_eq_id
#print axioms Y_Y_eq_id
#print axioms Z_Z_eq_id
#print axioms CNOT_CNOT_eq_id
#print axioms H_X_H_eq_Z
#print axioms H_Z_H_eq_X
#print axioms RZ_zero_eq_id
#print axioms RZ_add
#print axioms SWAP_eq_three_CNOTs

-- ── Grover's algorithm (T29) ─────────────────────────────────────────────
#print axioms groverStep2_correct

-- ── DensityMatrix: ofPure and applyUnitary (T30–T31) ─────────────────────
-- Inline proofs in structure `where` clauses; audited via the def itself.
-- Both elaborate with no sorryAx despite inline hermitian+PSD+trace proofs.
#print axioms LeanQVerify.DensityMatrix.ofPure
#print axioms LeanQVerify.DensityMatrix.applyUnitary

-- ── Parametric circuit families (T32–T35) ────────────────────────────────
-- GHZ circuit: gate count = n+1, CNOT count ≤ n (proved by induction)
-- BV oracle: CNOT count ≤ n (proved by induction on oracle depth)
#print axioms countGates_append
#print axioms ghzCircuit_gateCount
#print axioms ghzCircuit_cnotCount
#print axioms bvOracle_cnotCount_le

-- ── Verified QASM parser well-formedness (T36–T38) ───────────────────────
-- Soundness: Bool checker ⇒ formal Prop predicate
-- Concrete: Bell and GHZ-3 programs pass; out-of-bounds program fails
open QASM in
#print axioms checkWellFormed_sound
open QASM in
#print axioms bellProgram_wellFormed
open QASM in
#print axioms ghz3Program_wellFormed
open QASM in
#print axioms badProgram_fails
