import LeanQVerify.Circuit.Gate

/-!
# Quantum Circuits

A `QCircuit n` is a sequence of gates applied to an n-qubit system.
`denote` maps a circuit to its composite unitary matrix.
`CircuitEquiv` defines circuit equivalence as matrix equality.
-/

namespace LeanQVerify

open Matrix

/-- A quantum circuit for an n-qubit system: a list of gates. -/
inductive QCircuit (n : ℕ) : Type where
  | empty : QCircuit n
  | cons  : Gate n → QCircuit n → QCircuit n

namespace QCircuit

/-- Number of gates in the circuit. -/
def size {n : ℕ} : QCircuit n → ℕ
  | .empty     => 0
  | .cons _ c  => 1 + c.size

/-- Append two circuits: run c₁ then c₂. -/
def append {n : ℕ} : QCircuit n → QCircuit n → QCircuit n
  | .empty,     c₂ => c₂
  | .cons g c₁, c₂ => .cons g (c₁.append c₂)

instance {n : ℕ} : Append (QCircuit n) := ⟨append⟩

/-- Denotational semantics: maps a circuit to its 2^n × 2^n unitary matrix.
    Gates are applied left-to-right: the first gate in `cons g c` is applied first.
    In matrix terms: denote (cons g c) = (denote c) * (gate matrix of g).
    Reading right-to-left matches standard quantum circuit diagram convention. -/
noncomputable def denote {n : ℕ} : QCircuit n → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | .empty     => 1
  | .cons g c  => c.denote * g.matrix

/-- Circuit equivalence: two circuits implement the same unitary. -/
def equiv {n : ℕ} (c₁ c₂ : QCircuit n) : Prop :=
  c₁.denote = c₂.denote

notation:50 c₁ " ≅ " c₂ => QCircuit.equiv c₁ c₂

/-- Apply a circuit's unitary to a state vector. -/
noncomputable def applyTo {n : ℕ} (c : QCircuit n)
    (v : Fin (2 ^ n) → ℂ) : Fin (2 ^ n) → ℂ :=
  c.denote.mulVec v

-- ---------------------------------------------------------------------------
-- Basic circuit combinators
-- ---------------------------------------------------------------------------

/-- A single-gate circuit. -/
def ofGate {n : ℕ} (g : Gate n) : QCircuit n := .cons g .empty

/-- The identity circuit (empty). -/
def id {n : ℕ} : QCircuit n := .empty

-- ---------------------------------------------------------------------------
-- Semantic lemmas
-- ---------------------------------------------------------------------------

@[simp]
theorem denote_empty {n : ℕ} : (QCircuit.empty : QCircuit n).denote = 1 := rfl

@[simp]
theorem denote_cons {n : ℕ} (g : Gate n) (c : QCircuit n) :
    (QCircuit.cons g c).denote = c.denote * g.matrix := rfl

theorem denote_append {n : ℕ} (c₁ c₂ : QCircuit n) :
    (c₁.append c₂).denote = c₂.denote * c₁.denote := by
  induction c₁ with
  | empty      => simp [append, denote]
  | cons g c ih =>
    simp [append, denote, ih, mul_assoc]

/-- Sequential composition of circuits: apply c₁ first, then c₂. -/
theorem denote_seq {n : ℕ} (c₁ c₂ : QCircuit n) :
    (c₁ ++ c₂).denote = c₂.denote * c₁.denote :=
  denote_append c₁ c₂

-- ---------------------------------------------------------------------------
-- Standard named circuits
-- ---------------------------------------------------------------------------

/-- Bell state preparation circuit: H on qubit 0, then CNOT (0 → 1). -/
def bellPrep : QCircuit 2 :=
  .cons (.H 0) (.cons (.CNOT 0 1) .empty)

/-- GHZ state preparation for 3 qubits: H on 0, CNOT (0→1), CNOT (0→2). -/
def ghzPrep : QCircuit 3 :=
  .cons (.H 0) (.cons (.CNOT 0 1) (.cons (.CNOT 0 2) .empty))

end QCircuit
end LeanQVerify
