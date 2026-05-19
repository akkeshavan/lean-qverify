/-!
# Gate Algebra Theorems (T15–T24)

Paper section: §5, Table 1, rows T15–T24.

These are universal gate identities: they hold for any number of qubits `n`
and any valid qubit index `i` (or pair `i, j`).  The quantifiers are
explicit in the theorem statements below.
-/

import LeanQVerify.Circuit.Identities

open LeanQVerify QCircuit

-- T15: Hadamard is its own inverse.  H ∘ H = I.
example (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.H i)) ≅ QCircuit.id :=
  H_H_eq_id n i

-- T16: Pauli X is its own inverse.  X ∘ X = I.
example (n : ℕ) (i : Fin n) :
    (ofGate (.X i) ++ ofGate (.X i)) ≅ QCircuit.id :=
  X_X_eq_id n i

-- T17: Pauli Y is its own inverse.  Y ∘ Y = I.
example (n : ℕ) (i : Fin n) :
    (ofGate (.Y i) ++ ofGate (.Y i)) ≅ QCircuit.id :=
  Y_Y_eq_id n i

-- T18: Pauli Z is its own inverse.  Z ∘ Z = I.
example (n : ℕ) (i : Fin n) :
    (ofGate (.Z i) ++ ofGate (.Z i)) ≅ QCircuit.id :=
  Z_Z_eq_id n i

-- T19: CNOT applied twice is the identity.  CNOT ∘ CNOT = I.
example (n : ℕ) (c t : Fin n) (h : c ≠ t) :
    (ofGate (.CNOT c t) ++ ofGate (.CNOT c t)) ≅ QCircuit.id :=
  CNOT_CNOT_eq_id n c t h

-- T20: Hadamard conjugates X to Z.  H X H = Z.
example (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.X i) ++ ofGate (.H i)) ≅ ofGate (.Z i) :=
  H_X_H_eq_Z n i

-- T21: Hadamard conjugates Z to X.  H Z H = X.
example (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.Z i) ++ ofGate (.H i)) ≅ ofGate (.X i) :=
  H_Z_H_eq_X n i

-- T22: RZ with angle 0 is the identity.  RZ(0) = I.
example (n : ℕ) (i : Fin n) :
    ofGate (.RZ 0 i) ≅ QCircuit.id :=
  RZ_zero_eq_id n i

-- T23: Consecutive RZ rotations compose by angle addition.  RZ(θ) ∘ RZ(φ) = RZ(θ+φ).
example (n : ℕ) (i : Fin n) (θ φ : ℝ) :
    (ofGate (.RZ θ i) ++ ofGate (.RZ φ i)) ≅ ofGate (.RZ (θ + φ) i) :=
  RZ_add n i θ φ

-- T24: SWAP equals three CNOTs.  SWAP(i,j) = CNOT(i,j) ∘ CNOT(j,i) ∘ CNOT(i,j).
example (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    ofGate (.SWAP i j) ≅
    (ofGate (.CNOT i j) ++ ofGate (.CNOT j i) ++ ofGate (.CNOT i j)) :=
  SWAP_eq_three_CNOTs n i j h
