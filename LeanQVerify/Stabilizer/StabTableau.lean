import LeanQVerify.Stabilizer.CliffordGate

/-!
# Aaronson–Gottesman Stabilizer Tableau

Implements the binary symplectic representation from
"Improved Simulation of Stabilizer Circuits" (Aaronson–Gottesman 2004).

## Tableau layout

A `StabTableau n` has 2n rows:
- Rows 0..n-1   — destabilizer generators
- Rows n..2n-1  — stabilizer generators

Each row i encodes the Pauli operator
  (-1)^{phase[i]} · ⊗_j i^{x[i,j]·z[i,j]} X_j^{x[i,j]} Z_j^{z[i,j]},
i.e., a ±1-phased product of single-qubit Paulis over the n qubits.

## Step functions

Each Clifford gate g updates all 2n rows simultaneously according to
the 8 conjugation rules in A-G Table 1.  The computation is purely
Boolean — no complex arithmetic.

## Initial tableau

`ket0n n` represents |0^n⟩:
- Destabilizer row i: X_i (x[i,i]=1, all other bits 0)
- Stabilizer row n+i: Z_i (z[n+i,i]=1, all other bits 0)
-/

namespace LeanQVerify

-- ── Tableau data structure ────────────────────────────────────────────────────

/-- Stabilizer tableau for an n-qubit system. -/
structure StabTableau (n : ℕ) where
  x     : Fin (2 * n) → Fin n → Bool
  z     : Fin (2 * n) → Fin n → Bool
  phase : Fin (2 * n) → Bool

-- ── Initial tableau for |0^n⟩ ────────────────────────────────────────────────

/-- Initial tableau representing |0^n⟩.
    Stabilizer n+i: Z_i.  Destabilizer i: X_i. -/
def ket0n (n : ℕ) : StabTableau n where
  x     row qubit := row.val < n && (row.val == qubit.val)
  z     row qubit := n ≤ row.val && (row.val - n == qubit.val)
  phase _         := false

-- ── Phase update helpers (Table 1 of Aaronson–Gottesman 2004) ─────────────────

/-- Phase bit update for H on qubit a: flip when x[a]=1 AND z[a]=1. -/
def phaseH (xa za r : Bool) : Bool := r ^^ (xa && za)

/-- Phase bit update for S on qubit a: flip when x[a]=1 AND z[a]=1 (old z). -/
def phaseS (xa za r : Bool) : Bool := r ^^ (xa && za)

/-- Phase bit update for X on qubit a: flip when z[a]=1. -/
def phaseX (za r : Bool) : Bool := r ^^ za

/-- Phase bit update for Z on qubit a: flip when x[a]=1. -/
def phaseZ (xa r : Bool) : Bool := r ^^ xa

/-- Phase bit update for CNOT(control=a, target=b). -/
def phaseCNOT (xa za xb zb r : Bool) : Bool :=
  r ^^ (xa && zb && (xb ^^ za ^^ true))

-- ── Gate step functions ───────────────────────────────────────────────────────

/-- Apply H on qubit a: swap x[i,a] ↔ z[i,a] for all rows i. -/
def StabTableau.stepH {n : ℕ} (a : Fin n) (t : StabTableau n) : StabTableau n where
  x     row qubit := if qubit = a then t.z row qubit else t.x row qubit
  z     row qubit := if qubit = a then t.x row qubit else t.z row qubit
  phase row       := phaseH (t.x row a) (t.z row a) (t.phase row)

/-- Apply S on qubit a: z[i,a] ^= x[i,a] for all rows i. -/
def StabTableau.stepS {n : ℕ} (a : Fin n) (t : StabTableau n) : StabTableau n where
  x     row qubit := t.x row qubit
  z     row qubit := if qubit = a then t.z row qubit ^^ t.x row qubit else t.z row qubit
  phase row       := phaseS (t.x row a) (t.z row a) (t.phase row)

/-- Apply X on qubit a: flip phase when z[i,a]=1. -/
def StabTableau.stepX {n : ℕ} (a : Fin n) (t : StabTableau n) : StabTableau n where
  x     := t.x
  z     := t.z
  phase row := phaseX (t.z row a) (t.phase row)

/-- Apply Z on qubit a: flip phase when x[i,a]=1. -/
def StabTableau.stepZ {n : ℕ} (a : Fin n) (t : StabTableau n) : StabTableau n where
  x     := t.x
  z     := t.z
  phase row := phaseZ (t.x row a) (t.phase row)

/-- Apply CNOT(control=a, target=b):
    x[i,b] ^= x[i,a];  z[i,a] ^= z[i,b]. -/
def StabTableau.stepCNOT {n : ℕ} (a b : Fin n) (t : StabTableau n) : StabTableau n where
  x     row qubit := if qubit = b then t.x row qubit ^^ t.x row a else t.x row qubit
  z     row qubit := if qubit = a then t.z row qubit ^^ t.z row b else t.z row qubit
  phase row       := phaseCNOT (t.x row a) (t.z row a) (t.x row b) (t.z row b) (t.phase row)

/-- Dispatch a single Clifford gate to its step function. -/
def StabTableau.step {n : ℕ} (g : CliffordGate n) (t : StabTableau n) : StabTableau n :=
  match g with
  | .H q      => t.stepH q
  | .S q      => t.stepS q
  | .X q      => t.stepX q
  | .Z q      => t.stepZ q
  | .CNOT a b => t.stepCNOT a b

/-- Simulate a full Clifford circuit on the tableau (gates applied left-to-right). -/
def stabSim {n : ℕ} (c : CliffordCircuit n) (t : StabTableau n) : StabTableau n :=
  c.foldl (fun acc g => acc.step g) t

-- ── Structural lemmas ─────────────────────────────────────────────────────────

@[simp]
theorem stabSim_nil {n : ℕ} (t : StabTableau n) : stabSim [] t = t := rfl

@[simp]
theorem stabSim_cons {n : ℕ} (g : CliffordGate n) (c : CliffordCircuit n) (t : StabTableau n) :
    stabSim (g :: c) t = stabSim c (t.step g) := by
  simp [stabSim, List.foldl]

theorem stabSim_append {n : ℕ} (c₁ c₂ : CliffordCircuit n) (t : StabTableau n) :
    stabSim (c₁ ++ c₂) t = stabSim c₂ (stabSim c₁ t) := by
  simp only [stabSim]
  rw [List.foldl_append]

end LeanQVerify
