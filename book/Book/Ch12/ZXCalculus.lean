import LeanQVerify.ZX.GateTranslation

/-!
# Chapter 12 — ZX-Calculus

Read `prose.md` alongside this file.

ZX-calculus is a graphical language for quantum computation.
Circuits are diagrams; rewriting rules transform diagrams without
changing their matrix semantics.
-/

open LeanQVerify LeanQVerify.ZX ZXDiagram Real QCircuit

-- ── 1. Diagram types ──────────────────────────────────────────────────────────

-- ZXDiagram m n: a diagram with m inputs and n outputs.
#check (wire     : ZXDiagram 1 1)
#check (hadamard : ZXDiagram 1 1)
#check (zSpider 1 2 0 : ZXDiagram 1 2)   -- Z-spider: 1 input, 2 outputs, angle 0
#check (xSpider 2 1 0 : ZXDiagram 2 1)   -- X-spider: 2 inputs, 1 output, angle 0

-- ZX⟦d⟧ : the matrix semantics of diagram d.
-- Type: Matrix (Fin (2^n)) (Fin (2^m)) ℂ  for d : ZXDiagram m n
#check @ZXDiagram.denote

-- ── 2. Matrix semantics ───────────────────────────────────────────────────────

-- Wire is the identity:
example : ZX⟦wire⟧ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := denote_wire

-- Hadamard diagram is the H matrix:
example : ZX⟦hadamard⟧ = H_mat := denote_hadamard

-- Z-spider phase gates:
example : ZX⟦zSpider 1 1 Real.pi⟧ = Z_mat := by
  simp [denote_zSpider, zSpiderMat_11_pi]

example : ZX⟦zSpider 1 1 (Real.pi / 2)⟧ = S_mat := by
  simp [denote_zSpider, zSpiderMat_11_half_pi]

example : ZX⟦zSpider 1 1 (Real.pi / 4)⟧ = T_mat := by
  simp [denote_zSpider, zSpiderMat_11_quarter_pi]

-- X-spider with phase π is the X gate:
example : ZX⟦xSpider 1 1 Real.pi⟧ = X_mat := xSpider_pi_eq_X

-- ── 3. Fusion rule ────────────────────────────────────────────────────────────

-- Two X-spiders connected in series fuse into one with phases added.
-- Holds for all m, k, n ≥ 1.
#check @xSpider_fusion
-- xSpider_fusion : ∀ (m k n : ℕ), 0 < m → 0 < k → 0 < n → ∀ (α β : ℝ),
--   ZX⟦xSpider m k α ⊚ xSpider k n β⟧ = ZX⟦xSpider m n (α + β)⟧

-- Direct application:
example (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (α β : ℝ) :
    ZX⟦(xSpider m 1 α) ⊚ (xSpider 1 n β)⟧ =
    ZX⟦xSpider m n (α + β)⟧ :=
  xSpider_fusion m 1 n hm (by norm_num) hn α β

-- ── 4. π-copy rule ────────────────────────────────────────────────────────────

-- A Z(π) node commutes through an X-copy by duplicating onto both outputs.
-- This is a ZX rewrite rule: both sides have the same matrix semantics.
#check @pi_copy

example :
    ZX⟦(zSpider 1 1 Real.pi) ⊚ (xSpider 1 2 0)⟧ =
    ZX⟦(xSpider 1 2 0) ⊚ ((zSpider 1 1 Real.pi) ↑⊗ (zSpider 1 1 Real.pi))⟧ :=
  pi_copy

-- ── 5. Gate translation ───────────────────────────────────────────────────────

-- gateToZX₁ translates standard 1-qubit gates to ZX diagrams.
#check @gateToZX₁        -- Gate 1 → ZXDiagram 1 1
#check @isStdGate₁        -- which gates are supported: H/X/Z/S/T
#check @gateToZX₁_sound   -- ZX⟦gateToZX₁ g⟧ = g.matrix

-- H gate translates to hadamard:
example : ZX⟦gateToZX₁ (.H (⟨0, by norm_num⟩ : Fin 1))⟧ =
          (Gate.H (⟨0, by norm_num⟩ : Fin 1)).matrix :=
  gateToZX₁_sound _ trivial

-- Z gate translates to zSpider 1 1 π:
example : ZX⟦gateToZX₁ (.Z (⟨0, by norm_num⟩ : Fin 1))⟧ =
          (Gate.Z (⟨0, by norm_num⟩ : Fin 1)).matrix :=
  gateToZX₁_sound _ trivial

-- ── 6. Circuit translation ────────────────────────────────────────────────────

-- circuitToZX₁ folds gateToZX₁ over a QCircuit 1.
-- isStdCircuit₁ c checks that every gate in c is supported.
#check @circuitToZX₁
#check @circuitToZX₁_sound   -- ZX⟦circuitToZX₁ c⟧ = c.denote

-- The circuit [H; Z] on 1 qubit:
noncomputable def hzCircuit : QCircuit 1 :=
  .cons (.H ⟨0, by norm_num⟩) (.cons (.Z ⟨0, by norm_num⟩) .empty)

-- Its ZX translation is sound:
theorem hz_circuit_zx : ZX⟦circuitToZX₁ hzCircuit⟧ = hzCircuit.denote :=
  circuitToZX₁_sound hzCircuit ⟨trivial, trivial, trivial⟩
