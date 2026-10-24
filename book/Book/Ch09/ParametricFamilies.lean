import LeanQVerify.Circuit.Parametric
import LeanQVerify.Spec.StandardSpecs

/-!
# Chapter 9 — Parametric Circuit Families

Read `prose.md` in this directory alongside this file.

Parametric families are circuits defined for all n qubits.
Proving properties about them requires induction.
-/

open LeanQVerify QCircuit CircuitSpec

-- ── 1. The ghzCircuit family ──────────────────────────────────────────────────

-- ghzCircuit n produces an (n+1)-qubit circuit.
-- It prepares the GHZ state (|00…0⟩ + |11…1⟩)/√2.
#check @ghzCircuit   -- (n : ℕ) → QCircuit (n + 1)

-- Size of the GHZ circuit: n+1 gates (1 Hadamard + n CNOTs)
#check @ghzCircuit_gateCount
-- ∀ n, ghzCircuit n ⊨ totalGates (n + 1)

-- CNOT count: n CNOTs
#check @ghzCircuit_cnotCount
-- ∀ n, ghzCircuit n ⊨ maxCNOTs n

-- ── 2. Checking small cases ───────────────────────────────────────────────────

-- For n = 0: a 1-qubit circuit with 1 gate (just H)
example : ghzCircuit 0 ⊨ totalGates 1 := ghzCircuit_gateCount 0

-- For n = 1: a 2-qubit circuit with 2 gates (H + CNOT)
example : ghzCircuit 1 ⊨ totalGates 2 := ghzCircuit_gateCount 1

-- For n = 2: a 3-qubit circuit with 3 gates
example : ghzCircuit 2 ⊨ totalGates 3 := ghzCircuit_gateCount 2

-- All three follow from one theorem. Testing individual cases is not a proof.

-- ── 3. The BV oracle family ───────────────────────────────────────────────────

-- bvOracle n s constructs an n-qubit circuit for secret string s : Fin n → Bool
#check @bvOracle   -- (n : ℕ) → (Fin n → Bool) → QCircuit n

-- CNOT count: at most n (one per set bit in s)
#check @bvOracle_cnotCount_le
-- ∀ n s, bvOracle n s ⊨ maxCNOTs n

-- ── 4. The gate count addition lemma ─────────────────────────────────────────

-- countGates is additive over append:
-- countGates pred (c₁ ++ c₂) = countGates pred c₁ + countGates pred c₂
#check @countGates_append

-- This is used inside the induction proofs for ghzCircuit_gateCount.

-- ── 5. castSucc preserves structure ──────────────────────────────────────────

-- QCircuit.castSucc embeds an n-qubit circuit into (n+1) qubits.
-- The gate count and CNOT count are preserved.
#check @QCircuit.castSucc   -- QCircuit n → QCircuit (n+1)
