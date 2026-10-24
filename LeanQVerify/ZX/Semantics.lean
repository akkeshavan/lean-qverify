import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import LeanQVerify.ZX.Diagram
import LeanQVerify.Foundation.Unitary

/-!
# ZX-Calculus Matrix Semantics

Defines `ZXDiagram.denote d : Matrix (Fin (2^n)) (Fin (2^m)) ℂ` for every
`d : ZXDiagram m n`, giving the standard matrix interpretation of ZX diagrams.

## Key definitions

* `ZX.tensorMat` — Kronecker product re-indexed to `Fin (2^(n₁+n₂))`.
* `ZX.zSpiderMat` — Z-spider matrix: `|0⋯0⟩⟨0⋯0| + e^(iα)|1⋯1⟩⟨1⋯1|`.
* `ZX.hadN` — n-fold tensor of the Hadamard matrix.
* `ZXDiagram.denote` — recursive semantics.

## Conventions

* `ZXDiagram m n` maps `ℂ^(2^m)` to `ℂ^(2^n)`.
* Matrix type: `Matrix (Fin (2^n)) (Fin (2^m)) ℂ` (rows = outputs, cols = inputs).
* Sequential composition `d₁ ⊚ d₂` denotes as `⟦d₂⟧ * ⟦d₁⟧`.
* Tensor `d₁ ↑⊗ d₂` uses the Kronecker product with qubit ordering:
  qubits from d₁ occupy the high-order bits (big-endian within each group).
-/

namespace LeanQVerify.ZX

open LeanQVerify Complex Matrix BigOperators Kronecker

-- ============================================================
-- Helpers for re-indexing between Fin (2^n₁) × Fin (2^n₂)
-- and Fin (2^(n₁+n₂))
-- ============================================================

/-- The canonical bijection Fin (2^n₁) × Fin (2^n₂) ≃ Fin (2^(n₁+n₂)).
    Maps `(i, j)` to `i * 2^n₂ + j` (big-endian: n₁-group is high bits). -/
def finTwoPow_equiv (n₁ n₂ : ℕ) : Fin (2 ^ n₁) × Fin (2 ^ n₂) ≃ Fin (2 ^ (n₁ + n₂)) :=
  (finProdFinEquiv).trans (finCongr (pow_add 2 n₁ n₂).symm)

-- ============================================================
-- Kronecker / tensor product for ZX matrices
-- ============================================================

/-- Kronecker product of two ZX matrices, re-indexed from
    `Fin (2^n₁) × Fin (2^n₂)` to `Fin (2^(n₁+n₂))`. -/
noncomputable def tensorMat {n₁ m₁ n₂ m₂ : ℕ}
    (A : Matrix (Fin (2 ^ n₁)) (Fin (2 ^ m₁)) ℂ)
    (B : Matrix (Fin (2 ^ n₂)) (Fin (2 ^ m₂)) ℂ) :
    Matrix (Fin (2 ^ (n₁ + n₂))) (Fin (2 ^ (m₁ + m₂))) ℂ :=
  (A ⊗ₖ B).submatrix (finTwoPow_equiv n₁ n₂).symm (finTwoPow_equiv m₁ m₂).symm

-- ============================================================
-- Spider matrices
-- ============================================================

/-- Z-spider matrix with m inputs, n outputs, phase α.
    `zSpiderMat m n α [out][in] =
      1          if in = 0⋯0 and out = 0⋯0,
      e^(i·α)   if in = 1⋯1 and out = 1⋯1,
      0          otherwise.` -/
noncomputable def zSpiderMat (m n : ℕ) (α : ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ :=
  Matrix.of fun out inp =>
    if inp.val = 0 ∧ out.val = 0 then 1
    else if inp.val = 2 ^ m - 1 ∧ out.val = 2 ^ n - 1 then exp (I * ↑α)
    else 0

/-- n-fold Hadamard: the tensor product H ⊗ H ⊗ ⋯ ⊗ H (n times). -/
noncomputable def hadN : ∀ (n : ℕ), Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0     => 1
  | n + 1 => tensorMat (hadN n) H_mat

/-- X-spider matrix: conjugate the Z-spider by H⊗n on both sides. -/
noncomputable def xSpiderMat (m n : ℕ) (α : ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ :=
  hadN n * zSpiderMat m n α * hadN m

-- ============================================================
-- Cap, Cup, Swap matrices
-- ============================================================

/-- Cap matrix (0 inputs → 2 outputs): the vector |00⟩ + |11⟩.
    Encodes the (unnormalized) Bell state as a 4×1 column vector. -/
noncomputable def capMat : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 0)) ℂ :=
  Matrix.of fun out _ => if out.val = 0 ∨ out.val = 3 then 1 else 0

/-- Cup matrix (2 inputs → 0 outputs): the row vector ⟨00| + ⟨11|.
    Dual to cap; satisfies cap ∘ cup = 2·id and the zigzag equations. -/
noncomputable def cupMat : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 2)) ℂ :=
  Matrix.of fun _ inp => if inp.val = 0 ∨ inp.val = 3 then 1 else 0

/-- 2-qubit SWAP matrix (2 inputs → 2 outputs). -/
noncomputable def swapMat : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  embedSWAP 2 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩

-- ============================================================
-- Matrix semantics for ZXDiagram
-- ============================================================

/-- Denotational semantics: interpret a ZX diagram as a complex matrix.
    `ZXDiagram m n` → `Matrix (Fin (2^n)) (Fin (2^m)) ℂ`. -/
noncomputable def ZXDiagram.denote {m n : ℕ} (d : ZXDiagram m n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ :=
  match d with
  | .wire            => 1
  | .hadamard        => H_mat
  | .zSpider m' n' α => zSpiderMat m' n' α
  | .xSpider m' n' α => xSpiderMat m' n' α
  | .cap             => capMat
  | .cup             => cupMat
  | .swap            => swapMat
  | .compose d₁ d₂  => d₂.denote * d₁.denote
  | .tensor  d₁ d₂  => tensorMat d₁.denote d₂.denote

namespace ZXDiagram

/-- Notation for the matrix semantics.
    Uses `ZX⟦ d ⟧` to avoid conflict with Mathlib's global `⟦a⟧ = Quotient.mk _ a`. -/
notation "ZX⟦" d "⟧" => ZXDiagram.denote d

-- ============================================================
-- Basic semantic lemmas
-- ============================================================

/-- Wire denotes the 2×2 identity matrix. -/
@[simp] theorem denote_wire : ZX⟦(wire : ZXDiagram 1 1)⟧ = 1 := rfl

/-- Hadamard denotes the Hadamard matrix. -/
@[simp] theorem denote_hadamard : ZX⟦(hadamard : ZXDiagram 1 1)⟧ = H_mat := rfl

/-- Z-spider denotes its spider matrix. -/
@[simp] theorem denote_zSpider (m n : ℕ) (α : ℝ) :
    ZX⟦(zSpider m n α : ZXDiagram m n)⟧ = zSpiderMat m n α := rfl

/-- X-spider denotes its spider matrix. -/
@[simp] theorem denote_xSpider (m n : ℕ) (α : ℝ) :
    ZX⟦(xSpider m n α : ZXDiagram m n)⟧ = xSpiderMat m n α := rfl

/-- Sequential composition denotes as matrix product (right-to-left). -/
@[simp] theorem denote_compose {m k n : ℕ} (d₁ : ZXDiagram m k) (d₂ : ZXDiagram k n) :
    ZX⟦d₁ ⊚ d₂⟧ = ZX⟦d₂⟧ * ZX⟦d₁⟧ := rfl

/-- Tensor product denotes as Kronecker product. -/
@[simp] theorem denote_tensor {m₁ n₁ m₂ n₂ : ℕ}
    (d₁ : ZXDiagram m₁ n₁) (d₂ : ZXDiagram m₂ n₂) :
    ZX⟦d₁ ↑⊗ d₂⟧ = tensorMat ZX⟦d₁⟧ ZX⟦d₂⟧ := rfl

-- ============================================================
-- Z-spider special cases
-- ============================================================

/-- Z(1,1,0): the identity wire (Z-copy with phase 0 = |0⟩⟨0| + |1⟩⟨1| = I). -/
theorem zSpiderMat_11_zero : zSpiderMat 1 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSpiderMat, Matrix.one_apply]

/-- Z(1,1,π): the Z gate (Z-phase with phase π). -/
theorem zSpiderMat_11_pi : zSpiderMat 1 1 Real.pi = Z_mat := by
  have hexp : Complex.exp (Complex.I * Real.pi) = -1 := by
    rw [mul_comm]; exact Complex.exp_pi_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSpiderMat, Z_mat, hexp]

end ZXDiagram
end LeanQVerify.ZX
