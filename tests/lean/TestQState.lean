import LeanQVerify.Foundation.QState

/-!
# QState unit tests

Tests for basis state definitions and normalization.
-/

open LeanQVerify

-- ---------------------------------------------------------------------------
-- Basis states are defined
-- ---------------------------------------------------------------------------

#check QState.ket0      -- |0⟩
#check QState.ket1      -- |1⟩
#check QState.ketPlus   -- |+⟩ = (|0⟩ + |1⟩)/√2
#check QState.ketMinus  -- |−⟩ = (|0⟩ − |1⟩)/√2
#check QState.ket00     -- |00⟩
#check QState.ket01     -- |01⟩
#check QState.ket10     -- |10⟩
#check QState.ket11     -- |11⟩
#check QState.bellPhi   -- (|00⟩ + |11⟩)/√2

-- ---------------------------------------------------------------------------
-- QState is a subtype: val is the amplitude vector
-- ---------------------------------------------------------------------------

example : QState 1 := QState.ket0
example : QState 1 := QState.ket1
example : QState 2 := QState.ket00

-- ---------------------------------------------------------------------------
-- Fin indices for 1-qubit states
-- ---------------------------------------------------------------------------

-- ket0 has amplitude 1 at index 0, 0 at index 1
example : QState.ket0.val ⟨0, by norm_num⟩ = 1 := by
  unfold QState.ket0
  simp

example : QState.ket0.val ⟨1, by norm_num⟩ = 0 := by
  unfold QState.ket0
  simp

-- ket1 has amplitude 0 at index 0, 1 at index 1
example : QState.ket1.val ⟨0, by norm_num⟩ = 0 := by
  unfold QState.ket1
  simp

example : QState.ket1.val ⟨1, by norm_num⟩ = 1 := by
  unfold QState.ket1
  simp
