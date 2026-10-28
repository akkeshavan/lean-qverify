import LeanQVerify.Spec.CircuitSpec

/-!
# Verified Gate-by-Gate Circuit Evaluator

Phase 1 of the semantic automation roadmap.

`evalCircuit c ψ` applies circuit `c` to state `ψ` one gate at a time,
never building the full `2^n × 2^n` unitary matrix.  The bridge theorem
`evalCircuit_correct` proves it equals `c.applyTo ψ`.

Rewriting goals with `← evalCircuit_correct` lets the `verify_prob` tactic
reduce a semantic goal to a sequence of concrete matrix–vector products,
which `simp (decide := true)` then evaluates entry by entry.

## qverify_simps

`@[qverify_simps]` collects the simp lemmas used by `verify_prob`.
-/

namespace LeanQVerify

open Matrix Complex QCircuit CircuitSpec

-- ── qverify_simps simp attribute ─────────────────────────────────────────────

/-- Simp set for the `verify_prob` tactic.
    Extend with new gate types or state definitions as needed. -/
register_simp_attr qverify_simps

-- ── Gate-by-gate evaluator ────────────────────────────────────────────────────

/-- Gate-by-gate state evaluator: applies `cons g c` by first applying gate `g`,
    then evaluating the rest of `c`.  Never allocates a full unitary. -/
noncomputable def evalCircuit {n : ℕ} :
    QCircuit n → (Fin (2^n) → ℂ) → (Fin (2^n) → ℂ)
  | .empty,    ψ => ψ
  | .cons g c, ψ => evalCircuit c (g.matrix.mulVec ψ)

@[simp]
theorem evalCircuit_empty {n : ℕ} (ψ : Fin (2^n) → ℂ) :
    evalCircuit .empty ψ = ψ := rfl

@[simp]
theorem evalCircuit_cons {n : ℕ} (g : Gate n) (c : QCircuit n) (ψ : Fin (2^n) → ℂ) :
    evalCircuit (.cons g c) ψ = evalCircuit c (g.matrix.mulVec ψ) := rfl

-- ── Bridge theorems ───────────────────────────────────────────────────────────

/-- Gate-by-gate evaluation is semantically equivalent to `QCircuit.applyTo`. -/
theorem evalCircuit_correct {n : ℕ} (c : QCircuit n) (ψ : Fin (2^n) → ℂ) :
    evalCircuit c ψ = c.applyTo ψ := by
  induction c generalizing ψ with
  | empty =>
    simp [QCircuit.applyTo]
  | cons g c' ih =>
    rw [evalCircuit_cons, ih]
    simp only [QCircuit.applyTo, QCircuit.denote_cons]
    exact Matrix.mulVec_mulVec ψ c'.denote g.matrix

/-- Evaluation distributes over circuit append: run c₁ then c₂ step-by-step.
    This lets `verify_prob` handle `++` circuits without building the full matrix product. -/
@[simp]
theorem evalCircuit_append {n : ℕ} (c₁ c₂ : QCircuit n) (ψ : Fin (2^n) → ℂ) :
    evalCircuit (c₁ ++ c₂) ψ = evalCircuit c₂ (evalCircuit c₁ ψ) := by
  simp only [evalCircuit_correct, QCircuit.applyTo, QCircuit.denote_seq]
  exact (Matrix.mulVec_mulVec ψ c₂.denote c₁.denote).symm

/-- `applyTo` equals gate-by-gate evaluation; exposes `evalCircuit` to simp. -/
theorem applyTo_eq_evalCircuit {n : ℕ} (c : QCircuit n) (ψ : Fin (2^n) → ℂ) :
    c.applyTo ψ = evalCircuit c ψ := (evalCircuit_correct c ψ).symm

end LeanQVerify
