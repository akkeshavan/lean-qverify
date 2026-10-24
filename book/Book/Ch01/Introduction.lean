import LeanQVerify.Spec.StandardSpecs
import LeanQVerify.Circuit.Parametric
import LeanQVerify.Foundation.HoareLogic
import LeanQVerify.ZX.GateTranslation

/-!
# Chapter 1 — Introduction

Chapter 1 is conceptual. This file checks that the library compiled
and that the 40 proved theorems are accessible.

Read `prose.md` in this directory first.
-/

open LeanQVerify LeanQVerify.ZX

-- The 40 kernel-checked theorems — hover over any #check in VS Code
-- to see the full type.

-- Structural properties
#check @bellPrep_twoGates     -- Bell circuit: exactly 2 gates
#check @bellPrep_oneCNOT      -- Bell circuit: exactly 1 CNOT
#check @bellPrep_depth        -- Bell circuit: depth ≤ 2
#check @ghzPrep_threeGates    -- GHZ-3 circuit: exactly 3 gates
#check @hea4_gateCount        -- HEA-4: exactly 7 gates

-- Semantic properties
#check @bellPrep_entangled       -- P(qubit 0 = 0) ≥ 1/2 from |00⟩
#check @bellPrep_joint_ket00     -- P(|00⟩) ≥ 1/2 from |00⟩
#check @bellPrep_joint_ket11     -- P(|11⟩) ≥ 1/2 from |00⟩
#check @bellPrep_joint_ket01_zero -- P(|01⟩) = 0 from |00⟩
#check @groverStep2_correct      -- Grover step: P(target) ≥ 0.99

-- Gate algebra identities
#check @H_H_eq_id      -- H ∘ H ≅ I
#check @CNOT_CNOT_eq_id -- CNOT ∘ CNOT ≅ I
#check @RZ_zero_eq_id  -- RZ(0) ≅ I
#check @RZ_add         -- RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ)
#check @SWAP_eq_three_CNOTs -- SWAP ≅ CNOT³

-- Parametric families
#check @ghzCircuit_gateCount  -- ghzCircuit(n): n+1 gates, for all n
#check @ghzCircuit_cnotCount  -- ghzCircuit(n): n CNOTs, for all n
#check @bvOracle_cnotCount_le -- BV oracle(n,s): ≤ n CNOTs, for all n,s

-- Quantum Hoare Logic (Ch11)
#check @QPred            -- quantum predicate: Hermitian A with 0 ≤ A ≤ I
#check @HoareTriple      -- {A} c {B}: tr(Aρ) ≤ tr(B·c(ρ)) for all density ρ
#check @hoare_gate       -- {U†AU} gate(U) {A}

-- ZX-calculus (Ch12)
#check @gateToZX₁_sound     -- ZX⟦gateToZX₁ g⟧ = g.matrix
#check @circuitToZX₁_sound  -- ZX⟦circuitToZX₁ c⟧ = c.denote
#check @pi_copy              -- π-copy rule: Z(π) duplicates through X-copy
