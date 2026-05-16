import LeanQVerify.Circuit.QCircuit
import LeanQVerify.Foundation.DensityMatrix

/-!
# Circuit Specification Language

`CircuitSpec n` is the type of properties you can state about an n-qubit circuit.
`satisfies` is the satisfaction relation between a circuit and a spec.
-/

namespace LeanQVerify

open Matrix QCircuit

/-- Properties expressible about an n-qubit circuit. -/
inductive CircuitSpec (n : ℕ) : Type where
  /-- This circuit's unitary equals a given target matrix. -/
  | implementsMatrix : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → CircuitSpec n

  /-- This circuit is equivalent to another given circuit. -/
  | equivalentTo : QCircuit n → CircuitSpec n

  /-- Starting from input state ψ, measuring qubit i gives outcome b
      with probability at least p. -/
  | measurementProb :
      QState n           -- input state
      → Fin n            -- which qubit to measure
      → Bool             -- expected outcome (false = 0, true = 1)
      → ℝ                -- probability lower bound
      → CircuitSpec n

  /-- The number of gates satisfying pred is at most k. -/
  | gateCount : (Gate n → Bool) → ℕ → CircuitSpec n

  /-- The circuit depth is at most k. -/
  | maxDepth : ℕ → CircuitSpec n

  /-- Conjunction of two specs: both must hold. -/
  | both : CircuitSpec n → CircuitSpec n → CircuitSpec n

namespace CircuitSpec

-- ---------------------------------------------------------------------------
-- Convenience constructors
-- ---------------------------------------------------------------------------

/-- The circuit implements the identity. -/
def isIdentity (n : ℕ) : CircuitSpec n :=
  .implementsMatrix 1

/-- Equivalence to the Bell preparation circuit. -/
def isBellPrep : CircuitSpec 2 :=
  .equivalentTo QCircuit.bellPrep

/-- Total gate count is at most k. -/
def totalGates {n : ℕ} (k : ℕ) : CircuitSpec n :=
  .gateCount (fun _ => true) k

/-- Number of CNOT gates is at most k. -/
def maxCNOTs {n : ℕ} (k : ℕ) : CircuitSpec n :=
  .gateCount (fun g => match g with | .CNOT .. => true | _ => false) k

-- ---------------------------------------------------------------------------
-- Satisfaction relation
-- ---------------------------------------------------------------------------

/-- Count gates in a circuit satisfying a predicate. -/
def countGates {n : ℕ} (pred : Gate n → Bool) : QCircuit n → ℕ
  | .empty     => 0
  | .cons g c  => (if pred g then 1 else 0) + countGates pred c

/-- The set of qubit indices used by a gate. -/
def gateQubits {n : ℕ} : Gate n → Finset (Fin n)
  | .H  i       => {i}
  | .X  i       => {i}
  | .Y  i       => {i}
  | .Z  i       => {i}
  | .S  i       => {i}
  | .T  i       => {i}
  | .RX _ i     => {i}
  | .RY _ i     => {i}
  | .RZ _ i     => {i}
  | .CNOT c t   => {c, t}
  | .CZ  c t    => {c, t}
  | .SWAP i j   => {i, j}
  | .CCX c1 c2 t => {c1, c2, t}

/-- Track the earliest-available time for each qubit through a circuit.
    This is the inner loop of the list-scheduling depth algorithm. -/
def scheduleDepth {n : ℕ} : QCircuit n → (Fin n → ℕ) → ℕ
  | .empty,     ready => Finset.sup Finset.univ ready
  | .cons g c', ready =>
      let used := gateQubits g
      -- Gate starts when all its qubits are free
      let t    := used.sup ready
      -- After the gate, used qubits are busy until t+1
      scheduleDepth c' (fun i => if i ∈ used then t + 1 else ready i)

/-- Parallel depth of a circuit: the critical-path length under the assumption
    that gates on disjoint qubits execute simultaneously.
    Uses the standard list-scheduling algorithm (greedy, front-to-back). -/
def depth {n : ℕ} (c : QCircuit n) : ℕ := scheduleDepth c (fun _ => 0)

/-- Compute the probability of measuring outcome b on qubit i,
    given the state ψ after the circuit is applied. -/
noncomputable def measProb {n : ℕ}
    (c : QCircuit n) (ψ : QState n) (i : Fin n) (b : Bool) : ℝ :=
  -- Apply circuit to ψ to get the output state
  let output : Fin (2^n) → ℂ := c.applyTo ψ.val
  -- Sum probabilities of all basis states where bit i equals b
  ∑ k : Fin (2^n), if k.val.testBit i.val = b
    then Complex.normSq (output k)
    else 0

/-- A circuit satisfies a spec. -/
noncomputable def satisfies {n : ℕ} (c : QCircuit n) : CircuitSpec n → Prop
  | .implementsMatrix U       => c.denote = U
  | .equivalentTo c'          => c ≅ c'
  | .measurementProb ψ i b p  => p ≤ measProb c ψ i b
  | .gateCount pred k         => countGates pred c ≤ k
  | .maxDepth k               => depth c ≤ k
  | .both s₁ s₂               => satisfies c s₁ ∧ satisfies c s₂

end CircuitSpec

/-- Notation: `c ⊨ s` means circuit c satisfies spec s. -/
notation:40 c " ⊨ " s => CircuitSpec.satisfies c s

end LeanQVerify
