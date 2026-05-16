import LeanQVerify.Foundation.Unitary

/-!
# Quantum Gates

`Gate n` is an inductive type enumerating all supported gates for an n-qubit
system. `gateMatrix` maps each gate to its 2^n × 2^n unitary matrix.
-/

namespace LeanQVerify

open Matrix

/-- All supported quantum gates for an n-qubit system. -/
inductive Gate (n : ℕ) : Type where
  -- Single-qubit gates
  | H    : Fin n → Gate n              -- Hadamard
  | X    : Fin n → Gate n              -- Pauli X (NOT)
  | Y    : Fin n → Gate n              -- Pauli Y
  | Z    : Fin n → Gate n              -- Pauli Z
  | S    : Fin n → Gate n              -- S gate  (phase +i)
  | T    : Fin n → Gate n              -- T gate  (phase e^{iπ/4})
  | RX   : ℝ → Fin n → Gate n         -- Rx(θ)
  | RY   : ℝ → Fin n → Gate n         -- Ry(θ)
  | RZ   : ℝ → Fin n → Gate n         -- Rz(θ)
  -- Two-qubit gates
  | CNOT : Fin n → Fin n → Gate n     -- Controlled-NOT
  | CZ   : Fin n → Fin n → Gate n     -- Controlled-Z
  | SWAP : Fin n → Fin n → Gate n     -- SWAP
  -- Three-qubit gate
  | CCX  : Fin n → Fin n → Fin n → Gate n  -- Toffoli

namespace Gate

/-- Map each gate to its 2^n × 2^n complex matrix. -/
noncomputable def matrix {n : ℕ} : Gate n → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | .H  i      => embedGate1 n i H_mat
  | .X  i      => embedGate1 n i X_mat
  | .Y  i      => embedGate1 n i Y_mat
  | .Z  i      => embedGate1 n i Z_mat
  | .S  i      => embedGate1 n i S_mat
  | .T  i      => embedGate1 n i T_mat
  | .RX θ i    => embedGate1 n i (Rx_mat θ)
  | .RY θ i    => embedGate1 n i (Ry_mat θ)
  | .RZ θ i    => embedGate1 n i (Rz_mat θ)
  | .CNOT c t  => embedCNOT n c t
  | .CZ  c t   => embedCZ   n c t
  | .SWAP i j  => embedSWAP n i j
  | .CCX c1 c2 t => embedCCX n c1 c2 t

/-- Every gate matrix is its own inverse for self-inverse gates. -/
theorem X_self_inverse (n : ℕ) (i : Fin n) :
    (Gate.X i).matrix * (Gate.X i).matrix = (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by
  simp only [matrix]
  exact embedGate1_self_inverse n i X_mat X_mat_unitary

theorem Z_self_inverse (n : ℕ) (i : Fin n) :
    (Gate.Z i).matrix * (Gate.Z i).matrix = (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by
  simp only [matrix]
  exact embedGate1_self_inverse n i Z_mat Z_mat_unitary

theorem H_self_inverse (n : ℕ) (i : Fin n) :
    (Gate.H i).matrix * (Gate.H i).matrix = (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by
  simp only [matrix]
  exact embedGate1_self_inverse n i H_mat H_mat_unitary

theorem CNOT_self_inverse (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    (Gate.CNOT c t).matrix * (Gate.CNOT c t).matrix =
    (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) := by
  simp only [matrix]
  exact embedCNOT_self_mul n c t hct

end Gate
end LeanQVerify
