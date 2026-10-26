import LeanQVerify.Circuit.Gate
import LeanQVerify.Circuit.QCircuit

/-!
# Clifford Gate Subset and Circuit Classifier

Defines the Clifford-only gate type, the circuit-level type, and a
decision procedure that tries to extract a `CliffordCircuit` from a
general `QCircuit`.  The Clifford set {H, S, X, Z, CNOT} is closed
under composition and conjugation, and suffices to generate all
Clifford unitaries.

T, RZ, and rotation gates are **not** Clifford and cause `ofQCircuit?`
to return `none`.
-/

namespace LeanQVerify

/-- Clifford-only gate subset for n-qubit systems. -/
inductive CliffordGate (n : ℕ) where
  | H    : Fin n → CliffordGate n
  | S    : Fin n → CliffordGate n
  | X    : Fin n → CliffordGate n
  | Z    : Fin n → CliffordGate n
  | CNOT : Fin n → Fin n → CliffordGate n
  deriving DecidableEq

/-- Embed a Clifford gate into the general Gate type for matrix access. -/
def CliffordGate.toGate {n : ℕ} : CliffordGate n → Gate n
  | .H q      => .H q
  | .S q      => .S q
  | .X q      => .X q
  | .Z q      => .Z q
  | .CNOT a b => .CNOT a b

/-- A Clifford circuit: ordered list of Clifford gates (first gate = applied first). -/
abbrev CliffordCircuit (n : ℕ) := List (CliffordGate n)

namespace CliffordCircuit

/-- Embed a Clifford circuit into the general QCircuit type. -/
def toQCircuit {n : ℕ} : CliffordCircuit n → QCircuit n
  | []      => .empty
  | g :: gs => .cons g.toGate (toQCircuit gs)

/-- Try to classify a general QCircuit as Clifford.
    Returns `none` if any gate is non-Clifford (T, RZ, CZ, SWAP, …). -/
def ofQCircuit? {n : ℕ} : QCircuit n → Option (CliffordCircuit n)
  | .empty    => some []
  | .cons g c =>
      ofQCircuit? c |>.bind fun rest =>
        match g with
        | .H q      => some (.H q :: rest)
        | .S q      => some (.S q :: rest)
        | .X q      => some (.X q :: rest)
        | .Z q      => some (.Z q :: rest)
        | .CNOT a b => some (.CNOT a b :: rest)
        | _         => none

/-- `ofQCircuit?` is sound: if it succeeds, the embedded circuit equals the input. -/
theorem ofQCircuit?_sound {n : ℕ} (c : QCircuit n) (cc : CliffordCircuit n)
    (h : ofQCircuit? c = some cc) : cc.toQCircuit = c := by
  sorry

end CliffordCircuit
end LeanQVerify
