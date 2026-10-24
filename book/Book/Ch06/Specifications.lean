import LeanQVerify.Spec.CircuitSpec
import LeanQVerify.Spec.Satisfies
import LeanQVerify.Spec.StandardSpecs

/-!
# Chapter 6 — Specifications

Read `prose.md` in this directory alongside this file.
-/

open LeanQVerify QCircuit CircuitSpec

-- ── 1. The CircuitSpec type ────────────────────────────────────────────────────

#check @CircuitSpec   -- CircuitSpec : ℕ → Type

-- The satisfaction relation: circuit ⊨ spec
#check @satisfies    -- QCircuit n → CircuitSpec n → Prop

-- ── 2. Named spec constructors ────────────────────────────────────────────────

#check @totalGates   -- totalGates k : CircuitSpec n  (total gates = k)
#check @maxCNOTs     -- maxCNOTs k   : CircuitSpec n  (CNOT count ≤ k)
#check @maxRZGates   -- maxRZGates k : CircuitSpec n  (RZ count ≤ k)

-- ── 3. Building specs ─────────────────────────────────────────────────────────

-- A gate count spec
def spec_gateCount : CircuitSpec 2 := totalGates 2

-- A depth spec
def spec_depth : CircuitSpec 2 := .maxDepth 2

-- A measurement probability spec: P(qubit 0 = 0 | input |00⟩) ≥ 1/2
noncomputable def spec_prob : CircuitSpec 2 :=
  .measurementProb QState.ket00 ⟨0, by norm_num⟩ false (1/2)

-- Combining specs: both must hold
def spec_both : CircuitSpec 2 := .both spec_gateCount spec_depth

-- ── 4. Satisfaction for concrete circuits ─────────────────────────────────────

-- The Bell circuit satisfies the gate count spec
-- (the proof is a one-liner — see Chapter 7)
example : bellPrep ⊨ totalGates 2 := bellPrep_twoGates

-- ── 5. What ⊨ unfolds to ─────────────────────────────────────────────────────

-- For gateCount specs, satisfaction means:
--   countGates pred circuit ≤ k
-- For maxDepth specs, satisfaction means:
--   scheduleDepth circuit ≤ k
-- For measurementProb specs, satisfaction means:
--   normSq (circuit.applyTo input k) ≥ bound

-- The satisfies function handles each constructor differently.
#print satisfies
