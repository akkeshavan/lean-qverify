import LeanQVerify.ZX.CircuitToZX
import LeanQVerify.Circuit.QCircuit

/-!
# ZX-Calculus: Gate and Circuit Translation (1-qubit)

This module provides a certified translation from 1-qubit `QCircuit`s to
`ZXDiagram`s, with a matrix-level soundness proof.

## Scope

* `gateToZX₁`     — translate a standard 1-qubit gate to a ZX diagram.
* `gateToZX₁_sound` — `ZX⟦gateToZX₁ g⟧ = g.matrix` for supported gates.
* `circuitToZX₁`   — translate a 1-qubit circuit by folding gate translations.
* `circuitToZX₁_sound` — `ZX⟦circuitToZX₁ c⟧ = c.denote` for standard circuits.

## Supported gate set

H, X, Z, S, T (all standard Clifford/T single-qubit gates with direct Z-spider
or X-spider representations). Parametric and controlled gates are outside scope.
-/

namespace LeanQVerify.ZX

open ZXDiagram Complex Matrix Real BigOperators LeanQVerify QCircuit

-- ============================================================
-- Gate translation
-- ============================================================

/-- Gates that have a direct ZX-diagram translation. -/
def isStdGate₁ : Gate 1 → Prop
  | .H _ | .X _ | .Z _ | .S _ | .T _ => True
  | _ => False

/-- Translate a standard 1-qubit gate to its ZX diagram. -/
noncomputable def gateToZX₁ : Gate 1 → ZXDiagram 1 1
  | .H _ => hadamard
  | .X _ => xSpider 1 1 Real.pi
  | .Z _ => zSpider 1 1 Real.pi
  | .S _ => zSpider 1 1 (Real.pi / 2)
  | .T _ => zSpider 1 1 (Real.pi / 4)
  | _    => wire

/-- **Gate soundness**: `ZX⟦gateToZX₁ g⟧ = g.matrix` for all supported gates. -/
theorem gateToZX₁_sound (g : Gate 1) (hg : isStdGate₁ g) :
    ZX⟦gateToZX₁ g⟧ = g.matrix := by
  cases g with
  | H i =>
    fin_cases i
    simp only [gateToZX₁, denote_hadamard, Gate.matrix, embedGate1_one_qubit]
  | X i =>
    fin_cases i
    simp only [gateToZX₁, xSpider_pi_eq_X, Gate.matrix, embedGate1_one_qubit]
  | Z i =>
    fin_cases i
    simp only [gateToZX₁, denote_zSpider, zSpiderMat_11_pi, Gate.matrix, embedGate1_one_qubit]
  | S i =>
    fin_cases i
    simp only [gateToZX₁, denote_zSpider, zSpiderMat_11_half_pi, Gate.matrix, embedGate1_one_qubit]
  | T i =>
    fin_cases i
    simp only [gateToZX₁, denote_zSpider, zSpiderMat_11_quarter_pi, Gate.matrix, embedGate1_one_qubit]
  | Y _       => simp [isStdGate₁] at hg
  | RX _ _    => simp [isStdGate₁] at hg
  | RY _ _    => simp [isStdGate₁] at hg
  | RZ _ _    => simp [isStdGate₁] at hg
  | CNOT _ _  => simp [isStdGate₁] at hg
  | CZ _ _    => simp [isStdGate₁] at hg
  | SWAP _ _  => simp [isStdGate₁] at hg
  | CCX _ _ _ => simp [isStdGate₁] at hg
  | U3 _ _ _ _ => simp [isStdGate₁] at hg
  | CH _ _    => simp [isStdGate₁] at hg
  | CY _ _    => simp [isStdGate₁] at hg
  | CP _ _ _  => simp [isStdGate₁] at hg
  | CRZ _ _ _ => simp [isStdGate₁] at hg
  | RZZ _ _ _ => simp [isStdGate₁] at hg
  | RXX _ _ _ => simp [isStdGate₁] at hg
  | RYY _ _ _ => simp [isStdGate₁] at hg

-- ============================================================
-- Circuit translation
-- ============================================================

/-- Translate a 1-qubit circuit to a ZX diagram by sequential gate composition. -/
noncomputable def circuitToZX₁ : QCircuit 1 → ZXDiagram 1 1
  | .empty    => wire
  | .cons g c => gateToZX₁ g ⊚ circuitToZX₁ c

/-- A circuit is *standard* if every gate is in the supported gate set. -/
def isStdCircuit₁ : QCircuit 1 → Prop
  | .empty    => True
  | .cons g c => isStdGate₁ g ∧ isStdCircuit₁ c

/-- **Circuit soundness**: for any standard 1-qubit circuit,
    its ZX translation has identical matrix semantics. -/
theorem circuitToZX₁_sound (c : QCircuit 1) (hc : isStdCircuit₁ c) :
    ZX⟦circuitToZX₁ c⟧ = c.denote := by
  induction c with
  | empty =>
    simp [circuitToZX₁, denote_wire, denote_empty]
  | cons g c' ih =>
    obtain ⟨hg, hc'⟩ := hc
    simp only [circuitToZX₁, denote_compose, denote_cons]
    rw [ih hc', gateToZX₁_sound g hg]

end LeanQVerify.ZX
