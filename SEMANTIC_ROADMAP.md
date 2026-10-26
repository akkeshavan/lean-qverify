# Semantic Automation Roadmap — `lean-qverify`

Based on the deep-research review (Oct 2026) and collaborator critique.
Goal: turn `lean-qverify` into a **proof-producing semantic dispatcher**:

```
Qiskit circuit → classify → verified backend → Lean-kernel-checked certificate
```

---

## Architecture (target)

```
verify_prob (front-end tactic)
   │
   ├── Clifford circuit ──────► Stabilizer backend      (Phase 2)
   ├── small / exact circuit ─► Dense evaluator         (Phase 1) ← current
   ├── Clifford+T ────────────► Exact scalar backend    (Phase 3a)
   ├── concrete rotations ────► Interval backend        (Phase 3b)
   └── unsupported ───────────► emit for manual / LLM   (fallback)
```

Every backend produces a `SemanticCertificate` discharged by one soundness theorem.

---

## Phase 1 — Small-Circuit Dense Evaluator (`verify_prob`)

**Branch:** `feat/semantic-automation`  
**Status:** partially complete

### Done ✓

| Item | File | Notes |
|---|---|---|
| `evalCircuit` gate-by-gate state evaluator | `Tactic/EvalCircuit.lean` | never builds full 2^n unitary |
| `evalCircuit_correct` bridge theorem | `Tactic/EvalCircuit.lean` | `evalCircuit c ψ = c.applyTo ψ` |
| `qverify_simps` simp attribute | `Tactic/EvalCircuit.lean` | extensible simp set |
| `verify_prob` tactic (3-pass: simp + decide + norm_num) | `Tactic/VerifyProb.lean` | dispatches via `applyTo` + `evalCircuit` |
| `sqrt2_inv_mul_self`, `sqrt2_inv_mul_mul` helper lemmas | `Tactic/VerifyProb.lean` | eliminate `(↑√2)⁻¹` arithmetic from Pass 2 |
| `bellPrep_joint_ket00_auto` | `Tactic/VerifyProb.lean` | `jointMeasProb` |
| `bellPrep_joint_ket11_auto` | `Tactic/VerifyProb.lean` | `jointMeasProb` |
| `bellPrep_meas_q0_false_auto`, `bellPrep_meas_q0_true_auto` | `Tactic/VerifyProb.lean` | `measurementProb` (marginal) |
| `ghzPrep_joint_ket000_auto`, `ghzPrep_joint_ket111_auto` | `Tactic/VerifyProb.lean` | 3-qubit GHZ, `Fin.sum_univ_eight` |
| `groverStep2_correct_auto` | `Tactic/VerifyProb.lean` | 11-gate 2-qubit Grover, `measurementProb` |

### Still needed (Phase 1 completion)

- [ ] **CZ / SWAP gate coverage** — add dedicated demo theorems for CZ-only and SWAP-only circuits (both embedGate types are in the simp set but untested stand-alone).

- [ ] **RZ (exact angle) coverage** — `Rz_mat` entries involve `Complex.exp`, which
  `norm_num` cannot close generically. For the finite set of recognized angles
  (π, π/2, π/4, …) add concrete `Rz_mat_pi`, `Rz_mat_half_pi`, etc. simp lemmas.

- [ ] **Benchmark timing** — record proof-term size and Lean checking time for each
  demo theorem by qubit count and gate count. Feed into Phase 2 baseline.

---

## Phase 2 — Verified Stabilizer Backend (flagship research)

**Branch:** `feat/stabilizer-backend` (to be created)  
**Status:** not started  
**Paper angle:** "verified Aaronson–Gottesman tableau connected by refinement theorem
to lean-qverify's existing denotational semantics"

### Key types to define

```lean
-- Clifford-only gate subset
inductive CliffordGate (n : ℕ) where
  | H    : Fin n → CliffordGate n
  | S    : Fin n → CliffordGate n
  | X    : Fin n → CliffordGate n
  | Z    : Fin n → CliffordGate n
  | CNOT : Fin n → Fin n → CliffordGate n

-- Circuit over CliffordGate
def CliffordCircuit (n : ℕ) := List (CliffordGate n)

-- Aaronson–Gottesman tableau (2n rows: n stabilizers + n destabilizers)
structure StabTableau (n : ℕ) where
  xBits  : Fin (2 * n) → Fin n → Bool   -- X part of each row
  zBits  : Fin (2 * n) → Fin n → Bool   -- Z part of each row
  phase  : Fin (2 * n) → Bool           -- phase bit (0 = +1, 1 = -1)
```

### Key functions to implement

```lean
-- Single-gate tableau update (8 rules from Aaronson–Gottesman §4)
def StabTableau.step : CliffordGate n → StabTableau n → StabTableau n

-- Full circuit simulation
def stabSim : CliffordCircuit n → StabTableau n → StabTableau n

-- Measurement probability from tableau
def StabTableau.zProb (t : StabTableau n) (q : Fin n) (b : Bool) : ℚ
```

### Key theorems to prove

```lean
-- Representation predicate (tableau ↔ Hilbert-space state, up to global phase)
def Represents (t : StabTableau n) (ψ : Fin (2^n) → ℂ) : Prop

-- Core refinement theorem
theorem stabSim_correct (c : CliffordCircuit n) (t₀ : StabTableau n) (ψ : Fin (2^n) → ℂ)
    (h : Represents t₀ ψ) :
    Represents (stabSim c t₀) (c.toQCircuit.applyTo ψ)

-- Measurement correctness
theorem zProb_correct (t : StabTableau n) (ψ : Fin (2^n) → ℂ) (q : Fin n) (b : Bool)
    (h : Represents t ψ) :
    (t.zProb q b : ℝ) = measProb c ψ q b

-- Soundness: decision procedure → CircuitSpec satisfaction
theorem verify_stabilizer_prob_sound
    (c : CliffordCircuit n) (ψ : QState n) (q : Fin n) (b : Bool) (p : ℝ)
    (h : verifyStabilizerProb c ψ q b p = true) :
    c.toQCircuit ⊨ .measurementProb ψ q b p
```

### Clifford classifier (proof-producing)

```lean
-- Try to extract a Clifford circuit from a general QCircuit
def asClifford? : QCircuit n → Option (CliffordCircuit n)

-- Soundness: if classification succeeds, the circuits are semantically equal
theorem asClifford?_sound (c : QCircuit n) (cc : CliffordCircuit n)
    (h : asClifford? c = some cc) :
    cc.toQCircuit = c
```

### Integration into `verify_prob` dispatcher

Once Phase 2 is proved, `verify_prob` gains a new early branch:
```lean
-- if asClifford? succeeds → use stabSim path
-- else → fall through to dense evaluator
```

### Subtasks (ordered)

- [ ] Define `CliffordGate`, `CliffordCircuit`, `CliffordCircuit.toQCircuit`
- [ ] Define `StabTableau`; choose exact Aaronson–Gottesman row layout
- [ ] Implement `StabTableau.step` for H, S, X, Z, CNOT (5 rules each on all 2n rows)
- [ ] Implement `stabSim` by folding `step` over the circuit
- [ ] Define initial tableau for computational-basis input states
- [ ] Define `Represents` predicate (relate tableau to state vector, quotienting global phase)
- [ ] Prove `stabSim_correct` (the load-bearing refinement theorem)
- [ ] Implement `StabTableau.zProb` (deterministic iff stabilizer/destabilizer check)
- [ ] Prove `zProb_correct`
- [ ] Implement `asClifford?` classifier
- [ ] Prove `asClifford?_sound`
- [ ] Implement `verifyStabilizerProb` as a `Bool`-valued function
- [ ] Prove `verify_stabilizer_prob_sound`
- [ ] Integrate into `verify_prob` dispatch
- [ ] Demo: `ghzPrep 100 ⊨ .measurementProb ...` via stabilizer path
- [ ] Benchmark: tabulate qubit count vs. checking time for GHZ(n), random Clifford circuits

**Note:** Check Lean-QEC (May 2026) for reusable binary-symplectic definitions
before re-implementing stabilizer infrastructure from scratch.

---

## Phase 3a — Exact Clifford+T Scalar Backend

**Branch:** `feat/exact-clifford-t` (to be created)  
**Status:** not started

Amplitudes for Clifford+T circuits live in `ℤ[1/√2, i]`:
```
(a + b√2 + i(c + d√2)) / (√2)^k,   a,b,c,d ∈ ℤ, k ∈ ℕ
```

### Key type

```lean
structure CliffordTScalar where
  reNum  : Zsqrtd 2   -- a + b√2  (Mathlib already has this)
  imNum  : Zsqrtd 2   -- c + d√2
  denomPow : ℕ        -- denominator is (√2)^denomPow

def CliffordTScalar.toComplex : CliffordTScalar → ℂ
```

### Key lemmas

```lean
theorem add_sound  (x y : CliffordTScalar) : (x + y).toComplex = x.toComplex + y.toComplex
theorem mul_sound  (x y : CliffordTScalar) : (x * y).toComplex = x.toComplex * y.toComplex
theorem normSq_sound (x : CliffordTScalar) : normSq x.toComplex = x.normSq.toReal
```

### Subtasks

- [ ] Define `CliffordTScalar` using Mathlib's `Zsqrtd 2`
- [ ] Implement arithmetic (add, mul, neg, conj) with canonicalization
- [ ] Prove `add_sound`, `mul_sound`, `normSq_sound`
- [ ] Define gate matrices in `CliffordTScalar` for H, T, CNOT
- [ ] Implement `CliffordTScalar` version of `evalCircuit`
- [ ] Prove bridge: `CliffordTScalar evalCircuit = Complex evalCircuit`
- [ ] Integrate into `verify_prob` ("uses only H/T/CNOT → exact path")

---

## Phase 3b — Certified Interval Backend

**Branch:** can share with Phase 3a  
**Status:** not started

For circuits with arbitrary concrete rotation angles (RX/RY/RZ with float inputs).

### Key type

```lean
structure IntervalComplex where
  reLo reHi : ℚ
  imLo imHi : ℚ
  -- invariant: actual value lies in [reLo,reHi] × [imLo,imHi]
```

### Key capability

Given a concrete `θ : Float`:
1. Produce an interval `[lo, hi]` containing `sin(θ/2)` and `cos(θ/2)`
2. Evaluate gate matrix entries as `IntervalComplex`
3. Bound `normSq` of the output amplitude
4. Prove `p ≤ normSq_lo` → circuit satisfies `measurementProb ... p`

### Subtasks

- [ ] Define `IntervalComplex` and soundness predicate
- [ ] Prove `IntervalComplex` arithmetic lemmas (add, mul sound)
- [ ] Implement `sin`/`cos` interval enclosure using Taylor remainder
  (or reuse Mathlib's `polyrith` / `dyadic_interval` where applicable)
- [ ] Implement `IntervalComplex` version of `evalCircuit`
- [ ] Prove bridge: interval contains the true `Complex` amplitude
- [ ] Integrate into `verify_prob` ("has concrete float angles → interval path")

---

## `verify_prob` dispatcher target design

```lean
elab "verify_prob" : tactic => do
  normalizeGoal
  if ← tryStabilizerBackend then return        -- Phase 2
  if ← tryExactCliffordTBackend then return    -- Phase 3a
  if ← tryIntervalBackend then return          -- Phase 3b
  tryDenseSmallCircuitFallback                  -- Phase 1 (current)
```

---

## What to deprioritize

- **LLMs as core verifier** — use only as fallback proof search when all backends fail;
  QEDIA (Oct 2026) makes LLM-centric quantum proofs prior art.
- **Whole-program QHL** — keep existing `HoareLogic.lean` but don't expand it for
  probability verification; it belongs to compositional program correctness, not scalar
  measurement bounds.
- **ZX-calculus rewriting for probability** — keep `ZX/` for circuit equivalence;
  don't route scalar probability goals through ZX rewriting.

---

## Publication framing

Avoid: "first quantum verification in Lean" (QEDIA, Lean-QEC).  
Avoid: "LLM-driven quantum proofs" (QEDIA, MerLean).

Use: **"Proof-producing semantic dispatcher for Qiskit circuits in Lean 4"**

Contributions:
1. Verified gate-by-gate evaluator (`verify_prob`) eliminating hand-written matrix proofs
2. Verified stabilizer backend with semantic refinement theorem to denotational semantics
3. Exact Clifford+T and certified-interval backends for non-Clifford circuits
4. Benchmark: automatic semantic verification across circuit classes (GHZ, teleportation,
   Grover, HEA) by qubit count and T-count

Load-bearing theorem for the paper:
```lean
theorem stabSim_correct ... -- one theorem justifies thousands of auto-generated proofs
```
