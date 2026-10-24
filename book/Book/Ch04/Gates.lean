import LeanQVerify.Circuit.Gate
import LeanQVerify.Circuit.Identities

/-!
# Chapter 4 — Gates

Read `prose.md` in this directory alongside this file.
-/

open LeanQVerify

-- ── 1. Gate constructors ─────────────────────────────────────────────────────

-- Gates for a 2-qubit system
#check (Gate.H ⟨0, by norm_num⟩ : Gate 2)   -- Hadamard on qubit 0
#check (Gate.X ⟨1, by norm_num⟩ : Gate 2)   -- Pauli X on qubit 1
#check (Gate.CNOT ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ : Gate 2)  -- CNOT(ctrl=0, tgt=1)

-- Gates for a 3-qubit system
#check (Gate.CCX ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ : Gate 3)  -- Toffoli

-- Rotation gate: the angle is a real number
#check (Gate.RZ (Real.pi / 4) ⟨0, by norm_num⟩ : Gate 2)  -- RZ(π/4) on qubit 0

-- ── 2. Qubit indices are range-checked ──────────────────────────────────────

-- Fin n is the type of natural numbers < n.
-- This means out-of-range indices are rejected at compile time.

-- Gate.H ⟨5, _⟩ : Gate 3   ← won't compile: 5 < 3 is unprovable
-- Gate.H ⟨0, by norm_num⟩ : Gate 3   ← fine: 0 < 3

-- ── 3. Gate matrices ─────────────────────────────────────────────────────────

-- Every gate has a 2^n × 2^n unitary matrix
#check @Gate.matrix   -- Gate n → Matrix (Fin (2^n)) (Fin (2^n)) ℂ

-- The matrices are noncomputable (involve real-number sqrt, trig)
-- You can prove things about them but not #eval them.

-- ── 4. A matrix identity: H ∘ H = I ─────────────────────────────────────────

-- This is stated in the library at the 2×2 matrix level.
-- The circuit-level version is H_H_eq_id.
open LeanQVerify in
#check @H_H_eq_id   -- a QCircuit with two H gates ≅ identity circuit
