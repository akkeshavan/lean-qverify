import LeanQVerify.Spec.StandardSpecs

/-!
# Chapter 7 — Structural Proofs

Read `prose.md` in this directory alongside this file.

All proofs here are about circuit structure (gate counts, depth),
not about what the circuit computes.
-/

open LeanQVerify QCircuit CircuitSpec

-- ── 1. Gate count: the Bell circuit has 2 gates ───────────────────────────────

theorem my_bellPrep_twoGates : bellPrep ⊨ totalGates 2 := by
  simp [satisfies, countGates, bellPrep, totalGates]

-- The library's version is identical:
#check @bellPrep_twoGates

-- ── 2. CNOT count: the Bell circuit has 1 CNOT ───────────────────────────────

theorem my_bellPrep_oneCNOT : bellPrep ⊨ maxCNOTs 1 := by
  simp [satisfies, countGates, bellPrep, maxCNOTs]

-- ── 3. Depth: the Bell circuit has depth ≤ 2 ─────────────────────────────────

theorem my_bellPrep_depth : bellPrep ⊨ .maxDepth 2 := by
  simp [satisfies, depth, scheduleDepth, bellPrep, gateQubits]

-- ── 4. Combined spec: gate count AND depth ────────────────────────────────────

theorem my_bellPrep_structure :
    bellPrep ⊨ .both (totalGates 2) (.maxDepth 2) := by
  simp [satisfies, countGates, depth, scheduleDepth, bellPrep, totalGates, gateQubits]

-- ── 5. GHZ circuit gate count ─────────────────────────────────────────────────

theorem my_ghzPrep_threeGates : ghzPrep ⊨ totalGates 3 := by
  simp [satisfies, countGates, ghzPrep, totalGates]

-- ── 6. HEA-4 circuit: 4 RZ gates ─────────────────────────────────────────────

-- The HEA circuit is parameterized by four angles.
-- The RZ count does not depend on the angles.
theorem my_hea4_rzCount (θ₀ θ₁ θ₂ θ₃ : ℝ) : hea4 θ₀ θ₁ θ₂ θ₃ ⊨ maxRZGates 4 := by
  simp [satisfies, countGates, hea4, maxRZGates]
