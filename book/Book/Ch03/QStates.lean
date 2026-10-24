import LeanQVerify.Foundation.QState

/-!
# Chapter 3 — Quantum States

Read `prose.md` in this directory alongside this file.
-/

open LeanQVerify QState Complex

-- ── 1. The QState type ──────────────────────────────────────────────────────

-- A 1-qubit state has 2 amplitudes (indices 0 and 1)
#check (ket0 : QState 1)
#check (ket1 : QState 1)
#check (ketPlus : QState 1)

-- A 2-qubit state has 4 amplitudes (indices 0, 1, 2, 3)
#check (ket00 : QState 2)
#check (ket11 : QState 2)
#check (bellPhi : QState 2)

-- ── 2. Accessing amplitudes ─────────────────────────────────────────────────

-- The .val field is the amplitude function: Fin (2^n) → ℂ
#check @QState.val  -- QState.val : QState n → Fin (2^n) → ℂ

-- ── 3. Measurement probabilities ────────────────────────────────────────────

-- prob k = |amplitude_k|²  (Born rule)
#check @QState.prob

-- Two theorems true for every QState:
#check @QState.prob_nonneg   -- 0 ≤ prob k
#check @QState.prob_sum_one  -- ∑ k, prob k = 1

-- ── 4. Concrete probability computations ────────────────────────────────────

-- |0⟩ has probability 1 of measuring outcome 0
example : ket0.prob ⟨0, by norm_num⟩ = 1 := by
  simp [QState.prob, QState.ket0, Matrix.cons_val_zero, Complex.normSq_one]

-- |0⟩ has probability 0 of measuring outcome 1
example : ket0.prob ⟨1, by norm_num⟩ = 0 := by
  simp [QState.prob, QState.ket0, Matrix.cons_val_one, Matrix.head_cons,
        Complex.normSq_zero]

-- Probabilities always sum to 1 — holds for ket0 as an instance
example : ∑ k : Fin 2, ket0.prob k = 1 := ket0.prob_sum_one

-- ── 5. The normalization condition is part of the type ───────────────────────

-- You cannot have a QState with unnormalized amplitudes.
-- This does NOT typecheck (the norm proof would be false):
--   def bad : QState 1 := ⟨![2, 0], by simp ...⟩  -- simp would fail
