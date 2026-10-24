import Mathlib.Data.Real.Basic

/-!
# ZX-Calculus Diagram Type

Defines the inductive type `ZXDiagram m n` representing a ZX-calculus diagram with
`m` input wires and `n` output wires.  This is the syntactic layer; matrix semantics
live in `ZX.Semantics`.

## Conventions

* Wires run left (inputs) to right (outputs).
* `m` = number of input wires (left boundary).
* `n` = number of output wires (right boundary).
* Composition `d₁ ⊚ d₂` means d₁ first (left), d₂ second (right).
  Types: d₁ : ZXDiagram m k, d₂ : ZXDiagram k n.
* Tensor `d₁ ↑⊗ d₂` stacks d₁ on top of d₂ (inputs interleaved by n+m rule).
-/

namespace LeanQVerify.ZX

/-- A ZX-calculus diagram with `m` input wires and `n` output wires. -/
inductive ZXDiagram : (m : ℕ) → (n : ℕ) → Type where
  /-- Single identity wire (1 input, 1 output). -/
  | wire : ZXDiagram 1 1
  /-- Hadamard box (1 input, 1 output). -/
  | hadamard : ZXDiagram 1 1
  /-- Z-spider with m inputs, n outputs, phase α. -/
  | zSpider (m n : ℕ) (α : ℝ) : ZXDiagram m n
  /-- X-spider with m inputs, n outputs, phase α. -/
  | xSpider (m n : ℕ) (α : ℝ) : ZXDiagram m n
  /-- Cap: 0 inputs, 2 outputs — creates the (unnormalized) Bell state |00⟩+|11⟩. -/
  | cap : ZXDiagram 0 2
  /-- Cup: 2 inputs, 0 outputs — the Bell-pair post-selection dual to cap. -/
  | cup : ZXDiagram 2 0
  /-- Swap: 2 inputs, 2 outputs — exchanges two wires. -/
  | swap : ZXDiagram 2 2
  /-- Sequential composition: d₁ from m inputs to k wires, d₂ from k to n outputs. -/
  | compose : ZXDiagram m k → ZXDiagram k n → ZXDiagram m n
  /-- Parallel tensor product: stacks two diagrams side by side. -/
  | tensor : ZXDiagram m₁ n₁ → ZXDiagram m₂ n₂ → ZXDiagram (m₁ + m₂) (n₁ + n₂)

namespace ZXDiagram

/-- Sequential composition notation. -/
infixl:60 " ⊚ " => ZXDiagram.compose

/-- Parallel tensor product notation. -/
infixl:50 " ↑⊗ " => ZXDiagram.tensor

/-- Z-spider with zero phase (identity on one wire for m=n=1). -/
abbrev zWire := zSpider 1 1 0

/-- X-spider with zero phase (identity in the X basis). -/
abbrev xWire := xSpider 1 1 0

/-- n parallel identity wires.
    Uses `n+1 = n + 1` (definitional) by appending `wire` on the right. -/
def nWires : ∀ (n : ℕ), ZXDiagram n n
  | 0     => zSpider 0 0 0   -- empty diagram = scalar 1
  | n + 1 => nWires n ↑⊗ wire

end ZXDiagram
end LeanQVerify.ZX
