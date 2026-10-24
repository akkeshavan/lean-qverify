# lean-qverify Architecture

This document describes the internal design of the lean-qverify library: how the
pieces fit together, why key decisions were made, and where to look when extending
or debugging any part of the system.

---

## Contents

1. [System overview](#1-system-overview)
2. [Module map](#2-module-map)
3. [Core type system](#3-core-type-system)
4. [Gate matrices and embedding](#4-gate-matrices-and-embedding)
5. [Denotational semantics](#5-denotational-semantics)
6. [Specification language](#6-specification-language)
7. [Proof infrastructure](#7-proof-infrastructure)
8. [QASM pipeline](#8-qasm-pipeline)
9. [ZX-calculus](#9-zx-calculus)
10. [Quantum Hoare Logic](#10-quantum-hoare-logic)
11. [Python bridge](#11-python-bridge)
12. [Build system](#12-build-system)
13. [Invariants and design decisions](#13-invariants-and-design-decisions)

---

## 1. System overview

lean-qverify connects three worlds:

```
Qiskit (Python)          lean-qverify (Lean 4)          Lean kernel
─────────────────        ──────────────────────────     ─────────────
QuantumCircuit      →    QCircuit n / CircuitSpec   →   kernel check
qasm3.dumps()            QASM parser + elaborator        (C++, ~3k LOC)
                         ZX-calculus / QHL
```

**Two verification lanes:**

```
LANE A — automated structural checks (Python-driven)

  Qiskit circuit
      │  qiskit.qasm3.dumps()
      ▼
  QASM string
      │  LeanQVerify.QASM.Parser + Elaborator
      ▼
  QCircuit n term (Lean definition)
      │  lean_qverify/prover.py generates theorem + proof
      ▼
  lake env lean                →   Verdict.STRUCT_PROVED
  (kernel checks gate-count,
   depth proofs automatically)


LANE B — semantic proofs (developer writes Lean)

  QCircuit n
      │  c ⊨ spec  (satisfies relation)
      ▼
  Prop  ─── lake build ──►  kernel-checked theorem
```

Lane A proves structural properties (gate count, depth) automatically. Lane B is
for semantic properties (measurement probabilities, unitary equivalence) that
require a hand-written proof.

The trusted computing base for a verified result is:
- Lean's kernel (~3,000 lines of C++)
- The QASM parser (not formally verified — see §8)
- The angle recognizer in the elaborator (float → exact ℝ)

---

## 2. Module map

```
lean-qverify/
├── LeanQVerify/
│   ├── Foundation/
│   │   ├── QState.lean          -- normalised state vectors and basis states
│   │   ├── Unitary.lean         -- gate matrices (2×2) and n-qubit embeddings
│   │   ├── DensityMatrix.lean   -- density matrix formalism (ρ, applyUnitary, measure)
│   │   └── HoareLogic.lean      -- QPred, HoareTriple, proof rules
│   ├── Circuit/
│   │   ├── Gate.lean            -- Gate n inductive type; Gate.matrix
│   │   ├── QCircuit.lean        -- QCircuit n; denote; append; identity
│   │   ├── Identities.lean      -- proved gate identity theorems (T15–T24)
│   │   └── Parametric.lean      -- parametric families (ghzCircuit n)
│   ├── Spec/
│   │   ├── CircuitSpec.lean     -- CircuitSpec n; satisfies; countGates; depth
│   │   ├── Satisfies.lean       -- monotonicity lemmas for satisfaction
│   │   └── StandardSpecs.lean   -- Bell, GHZ, teleportation, HEA, Grover theorems
│   ├── QASM/
│   │   ├── Parser.lean          -- recursive-descent QASM 3 parser
│   │   ├── Elaborator.lean      -- AST → ElabResult / QCircuit n; angle recognizer
│   │   ├── ParseTheorems.lean   -- correctness theorems for the parser
│   │   └── Serializer.lean      -- QCircuit n → QASM string
│   └── ZX/
│       ├── Diagram.lean         -- ZXDiagram m n inductive type; ⊚ ; ↑⊗
│       ├── Semantics.lean       -- ZX⟦·⟧ : ZXDiagram m n → Matrix ... ℂ
│       ├── Rules.lean           -- spider fusion, π-copy, colour change
│       └── GateTranslation.lean -- gateToZX₁, circuitToZX₁, soundness proofs
├── lean_qverify/                -- Python package
│   ├── bridge.py                -- Qiskit → lean-qverify-check integration
│   ├── prover.py                -- structural spec proof pipeline
│   ├── result.py                -- VerifyResult, Verdict enum
│   ├── runner.py                -- CLI entry point
│   ├── counterexample.py        -- numerical counterexample search (Qiskit Aer)
│   ├── simulator.py             -- CPU/GPU Aer backend selector
│   └── gpu.py                   -- GPU detection (CUDA threshold logic)
├── tests/
│   ├── lean/                    -- Lean unit tests (TestParser, TestCircuit, ...)
│   └── python/                  -- pytest suite
├── theorems/                    -- independent verification artifact
├── book/                        -- 12-chapter interactive book
├── benchmarks/                  -- 32 QASM benchmark circuits
└── docs/                        -- GitHub Pages site
```

---

## 3. Core type system

### 3.1 Gate n

`Gate n` is an inductive type parameterised by the number of qubits `n`:

```lean
inductive Gate (n : ℕ) : Type where
  | H   : Fin n → Gate n                    -- Hadamard
  | X   : Fin n → Gate n                    -- Pauli X
  | Y   : Fin n → Gate n                    -- Pauli Y
  | Z   : Fin n → Gate n                    -- Pauli Z
  | S   : Fin n → Gate n                    -- S gate (phase +i)
  | T   : Fin n → Gate n                    -- T gate (phase e^{iπ/4})
  | RX  : ℝ → Fin n → Gate n               -- Rx(θ)
  | RY  : ℝ → Fin n → Gate n               -- Ry(θ)
  | RZ  : ℝ → Fin n → Gate n               -- Rz(θ)
  | CNOT : Fin n → Fin n → Gate n          -- Controlled-NOT
  | CZ   : Fin n → Fin n → Gate n          -- Controlled-Z
  | SWAP : Fin n → Fin n → Gate n          -- SWAP
  | CCX  : Fin n → Fin n → Fin n → Gate n  -- Toffoli
  | U3   : ℝ → ℝ → ℝ → Fin n → Gate n    -- U3(θ,φ,λ) universal gate
  | CH   : Fin n → Fin n → Gate n          -- Controlled-H
  | CY   : Fin n → Fin n → Gate n          -- Controlled-Y
  | CP   : ℝ → Fin n → Fin n → Gate n     -- Controlled-phase(θ)
  | CRZ  : ℝ → Fin n → Fin n → Gate n     -- Controlled-Rz(θ)
  | RZZ  : ℝ → Fin n → Fin n → Gate n     -- exp(-iθ/2 · Z⊗Z)
  | RXX  : ℝ → Fin n → Fin n → Gate n     -- exp(-iθ/2 · X⊗X)
  | RYY  : ℝ → Fin n → Fin n → Gate n     -- exp(-iθ/2 · Y⊗Y)
```

Qubit indices are `Fin n`, so out-of-bounds indices are impossible at the type level.
There is no runtime bounds check. An expression like `.H (⟨5, by norm_num⟩ : Fin 3)`
is a type error at elaboration time.

Angles are `ℝ` (exact real numbers), not `Float`. This is what makes norm_num proofs
possible: `Real.pi / 2` can be manipulated symbolically, while `1.5707963...` cannot.

### 3.2 QCircuit n

```lean
inductive QCircuit (n : ℕ) : Type where
  | empty : QCircuit n
  | cons  : Gate n → QCircuit n → QCircuit n
```

A circuit is a cons-list of gates. `cons g c` means "apply g first, then c".
The head of the list is the first gate applied to the input state.

Key derived operations:

| Operation | Type | Definition |
|---|---|---|
| `size` | `QCircuit n → ℕ` | count gates |
| `append` | `QCircuit n → QCircuit n → QCircuit n` | run first, then second |
| `denote` | `QCircuit n → Matrix (Fin (2^n)) (Fin (2^n)) ℂ` | composite unitary |
| `identity` | `QCircuit n` | `.empty` (the no-op circuit) |
| `ofGate g` | `QCircuit n` | `.cons g .empty` |
| `applyTo` | `QCircuit n → (Fin (2^n) → ℂ) → (Fin (2^n) → ℂ)` | apply to state vector |

### 3.3 QState n

```lean
structure QState (n : ℕ) where
  val  : Fin (2^n) → ℂ
  norm : ‖val‖ = 1
```

A normalised state vector of dimension 2^n. The `norm` field is a proof that
the vector has unit norm — carried at type level, not checked at runtime.

Basis states like `ket00 : QState 2` are defined by explicit vectors
with norm proofs closed by `norm_num`.

### 3.4 DensityMatrix n

```lean
structure DensityMatrix (n : ℕ) where
  mat : Matrix (Fin (2^n)) (Fin (2^n)) ℂ
  herm : mat.IsHermitian
  psd  : ∀ x, 0 ≤ (dotProduct (star x) (mat.mulVec x)).re
  trace1 : mat.trace = 1
```

The density matrix formalism is used by Quantum Hoare Logic but not by the main
circuit theorems. `applyUnitary` requires an explicit proof of unitarity:

```lean
def applyUnitary (ρ : DensityMatrix n)
    (U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hU : U.conjTranspose * U = 1) : DensityMatrix n
```

This design means callers must supply a proof — a misuse (applying a non-unitary
matrix) is a type error.

**Known stub:** `measure` returns correct Born-rule probabilities but the
post-measurement density matrices are placeholders (both outcomes return `ρ`).
This is documented and not used by any proved theorem.

---

## 4. Gate matrices and embedding

### 4.1 2×2 matrices

All single-qubit gates are defined as concrete 2×2 matrices over ℂ in
`Unitary.lean`. Examples:

```lean
noncomputable def H_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := (Real.sqrt 2 : ℝ)⁻¹
  !![s, s; s, -s]

def X_mat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

noncomputable def Rz_mat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ Complex.exp (-I * θ/2), 0;
      0,                       Complex.exp (I * θ/2) ]
```

Self-inverse proofs (`H_mat_unitary`, `X_mat_unitary`, etc.) are proved by
`norm_num` or `ring` on explicit matrix entries.

### 4.2 Embedding single-qubit gates into 2^n space

The key challenge: a single-qubit gate acting on qubit `i` of an n-qubit system
must produce a `2^n × 2^n` matrix. This is done by `embedGate1`:

```lean
noncomputable def embedGate1 (n : ℕ) (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  Matrix.of fun row col =>
    if sameExcept row.val col.val i.val
    then M (natBit row.val i.val) (natBit col.val i.val)
    else 0
```

The matrix entry `(row, col)` is non-zero only when `row` and `col` differ at most
in bit `i`. The value is taken from `M` indexed by bit `i` of `row` and `col`.

**Key helper: `sameExcept`**

```lean
def sameExcept (j k i : ℕ) : Bool :=
  ∀ l, l ≠ i → j.testBit l = k.testBit l
```

This is private to `Unitary.lean` because it leaks bit-manipulation details.
The public interface is `embedGate1_one_qubit` (used in book chapter proofs):

```lean
lemma embedGate1_one_qubit (i : Fin 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 1 i M = M.reindex finSuccEquiv finSuccEquiv
```

### 4.3 Embedding CNOT and two-qubit gates

CNOT is not a tensor product, so it needs its own embedding. `embedCNOT n c t`
constructs a `2^n × 2^n` matrix where the `t`-th bit is flipped iff the `c`-th
bit is 1:

```lean
noncomputable def embedCNOT (n : ℕ) (c t : Fin n) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  Matrix.of fun row col =>
    let ctrl := row.val.testBit c.val
    if ctrl then
      -- control is 1: target bit must be flipped
      if col.val = row.val ^^^ (1 <<< t.val) then 1 else 0
    else
      -- control is 0: pass through unchanged
      if col.val = row.val then 1 else 0
```

Two-qubit rotation gates (`embedRZZ`, `embedRXX`, `embedRYY`) are defined by parity:

- `RZZ(θ)`: even-parity pairs (bits equal) → `exp(-iθ/2)`, odd parity → `exp(+iθ/2)`
- `RYY(θ)`: `|00⟩↔|11⟩` gets `+i·sin(θ/2)`, `|01⟩↔|10⟩` gets `-i·sin(θ/2)`

### 4.4 The `embedGate1_mul` lemma

The core lemma that makes gate identity proofs work:

```lean
theorem embedGate1_mul (n : ℕ) (i : Fin n)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i A * embedGate1 n i B = embedGate1 n i (A * B)
```

This means: applying gate A then gate B on qubit i is the same as applying the
composed gate A·B on qubit i. It reduces n-qubit proofs to 2×2 proofs.

Derived corollary:

```lean
theorem embedGate1_self_inverse (n : ℕ) (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M * M = 1) :
    embedGate1 n i M * embedGate1 n i M = 1 :=
  by rw [embedGate1_mul, h, embedGate1_one]
```

This is the proof skeleton for H∘H=I, X∘X=I, Y∘Y=I, Z∘Z=I.

---

## 5. Denotational semantics

```lean
noncomputable def denote {n : ℕ} : QCircuit n → Matrix (Fin (2^n)) (Fin (2^n)) ℂ
  | .empty     => 1
  | .cons g c  => c.denote * g.matrix
```

**Convention:** `cons g c` means "apply g first, then c". In the matrix product
`c.denote * g.matrix`, matrix multiplication is right-to-left (standard convention:
the rightmost matrix is applied first). Reading `c.denote * g.matrix` left-to-right
matches the circuit diagram: g is leftmost in the circuit, g.matrix is rightmost
in the product.

**`denote_seq` (the key composition theorem):**

```lean
theorem denote_seq {n : ℕ} (c₁ c₂ : QCircuit n) :
    (c₁ ++ c₂).denote = c₂.denote * c₁.denote
```

Appending c₁ then c₂ produces the matrix product c₂·c₁. This is proved by
induction on c₁ using `mul_assoc`.

**Circuit equivalence:**

```lean
def equiv {n : ℕ} (c₁ c₂ : QCircuit n) : Prop :=
  c₁.denote = c₂.denote

notation:50 c₁ " ≅ " c₂ => QCircuit.equiv c₁ c₂
```

---

## 6. Specification language

### 6.1 CircuitSpec n

```lean
inductive CircuitSpec (n : ℕ) : Type where
  | implementsMatrix : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → CircuitSpec n
  | equivalentTo     : QCircuit n → CircuitSpec n
  | measurementProb  : QState n → Fin n → Bool → ℝ → CircuitSpec n
  | jointMeasProb    : QState n → Fin (2^n) → ℝ → CircuitSpec n
  | gateCount        : (Gate n → Bool) → ℕ → CircuitSpec n
  | maxDepth         : ℕ → CircuitSpec n
  | both             : CircuitSpec n → CircuitSpec n → CircuitSpec n
```

The `⊨` notation connects a circuit to a spec:

```lean
def satisfies {n : ℕ} (c : QCircuit n) : CircuitSpec n → Prop
  | .implementsMatrix U => c.denote = U
  | .equivalentTo c'    => c.denote = c'.denote
  | .measurementProb ψ i b p => p ≤ measProb c ψ i b
  | .jointMeasProb ψ k p    => p ≤ jointMeasProb c ψ k
  | .gateCount pred k       => countGates pred c ≤ k
  | .maxDepth k             => depth c ≤ k
  | .both s₁ s₂             => satisfies c s₁ ∧ satisfies c s₂

notation:50 c " ⊨ " s => QCircuit.satisfies c s
```

### 6.2 Gate count

```lean
def countGates {n : ℕ} (pred : Gate n → Bool) : QCircuit n → ℕ
  | .empty     => 0
  | .cons g c  => (if pred g then 1 else 0) + countGates pred c
```

Structural recursion on the circuit list. For a concrete circuit and predicate,
`simp [countGates, circuit_def]` evaluates this to a numeral.

Convenience aliases:
- `totalGates k` = `gateCount (fun _ => true) k`
- `maxCNOTs k`   = `gateCount (fun g => match g with | .CNOT .. => true | _ => false) k`
- `maxRZGates k` = `gateCount (fun g => match g with | .RZ .. => true  | _ => false) k`

### 6.3 Depth algorithm

The depth implementation uses a list-scheduling algorithm (greedy, front-to-back):

```lean
def scheduleDepth {n : ℕ} : QCircuit n → (Fin n → ℕ) → ℕ
  | .empty,     ready => Finset.sup Finset.univ ready
  | .cons g c', ready =>
      let used := gateQubits g
      let t    := used.sup ready          -- gate starts when all its qubits are free
      scheduleDepth c' (fun i => if i ∈ used then t + 1 else ready i)

def depth {n : ℕ} (c : QCircuit n) : ℕ := scheduleDepth c (fun _ => 0)
```

`gateQubits : Gate n → Finset (Fin n)` maps each gate constructor to the set of
qubit indices it uses. Single-qubit gates return a singleton; two-qubit gates return
a two-element set.

For concrete circuits with concrete qubit counts, `simp [depth, scheduleDepth, gateQubits, circuit_def]` evaluates the entire computation to a numeral.

### 6.4 Measurement probability

```lean
noncomputable def measProb {n : ℕ}
    (c : QCircuit n) (ψ : QState n) (i : Fin n) (b : Bool) : ℝ :=
  let output : Fin (2^n) → ℂ := c.applyTo ψ.val
  ∑ k : Fin (2^n), if k.val.testBit i.val = b
    then Complex.normSq (output k)
    else 0
```

Measurement probability is the sum of `|amplitude|²` over all basis states where
bit `i` equals outcome `b`. This is the Born rule.

For the `jointMeasProb` variant (measuring all n qubits, getting a specific basis
state `k`):

```lean
noncomputable def jointMeasProb {n : ℕ}
    (c : QCircuit n) (ψ : QState n) (k : Fin (2^n)) : ℝ :=
  Complex.normSq ((c.applyTo ψ.val) k)
```

Probability of a single basis outcome is `|⟨k|ψ_out⟩|²`.

---

## 7. Proof infrastructure

### 7.1 Gate identity proof pattern

All gate self-inverse theorems (H∘H=I, X∘X=I, etc.) follow the same skeleton:

1. `denote_seq c₁ c₂` — reduce `(c₁ ++ c₂).denote` to `c₂.denote * c₁.denote`
2. `Gate.matrix` unfolding — replace `.matrix` with the concrete `embedGate1` call
3. `embedGate1_mul` — reduce the n-qubit product to a 2×2 product
4. 2×2 self-inverse lemma — close by `norm_num` or `ring`

Example (`H_H_eq_id`):

```lean
theorem H_H_eq_id (n : ℕ) (i : Fin n) :
    (ofGate (.H i) ++ ofGate (.H i)) ≅ QCircuit.identity :=
  embedGate1_self_inverse n i H_mat_unitary
```

### 7.2 Simp sets for automated proofs

Three standard simp sets are used throughout:

| Goal | Simp set |
|---|---|
| Gate count | `[satisfies, countGates, circuit_def]` |
| Depth | `[satisfies, depth, scheduleDepth, gateQubits, circuit_def]` |
| Measurement probability | expand by hand, then `norm_num` on individual entries |

The `circuit_def` (e.g., `bellPrep`) unfolds the circuit list so that `countGates`
and `scheduleDepth` can evaluate fully. For concrete circuits with small qubit counts,
`simp` evaluates everything to a numeral and closes the goal.

### 7.3 norm_num for measurement proofs

Measurement probability proofs expand the 2^n × 2^n unitary matrix, apply it to the
input state, and compute `|amplitude|²` for specific basis states. The steps are:

1. `show p ≤ Complex.normSq (output k)` — reduce to a single amplitude
2. `simp [applyTo, denote, Gate.matrix, embedGate1, ...]` — evaluate the matrix product
3. `norm_num [Real.sqrt_two_mul_self]` — close the arithmetic inequality

This is the most computation-heavy step. A 4-qubit circuit produces a 16×16 matrix;
Lean's kernel evaluates it at check time.

### 7.4 `linarith` and `nlinarith` for conjugation identities

Proofs like `H∘X∘H = Z` expand to matrix entry equalities. `nlinarith` closes
goals that involve `Real.sqrt` terms (like `(1/√2)·(1/√2) = 1/2`).

### 7.5 `Nat.testBit_xor` for SWAP

The SWAP = CNOT∘CNOT∘CNOT proof works by showing that XOR-ing bits twice returns
the original value. The key lemma is `Nat.testBit_xor`, which lets the proof
collapse a sum over basis states.

---

## 8. QASM pipeline

### 8.1 Parsing (Parser.lean)

The parser is a handwritten recursive-descent parser. It is **not formally verified**
— it is a trusted bridge component.

**AST types:**

```lean
inductive GateApp : Type where
  | h    : QubitRef → GateApp
  | cx   : QubitRef → QubitRef → GateApp
  | rx   : Float → QubitRef → GateApp
  | rz   : Float → QubitRef → GateApp
  | u3   : Float → Float → Float → QubitRef → GateApp
  -- ... (all 22 supported gates)
  | skipped : String → GateApp   -- unsupported gate, produces a warning
```

Qubit references are `{ reg : String, index : ℕ }`. The parser preserves register
names; the elaborator resolves them to global qubit indices.

Unsupported constructs (classical control, measurement, custom gate definitions) are
skipped rather than failing. This allows partial parsing of circuits that contain
unsupported features — the supported gates are still elaborated.

### 8.2 Elaboration (Elaborator.lean)

The elaborator converts a `QASMProgram` (list of `GateApp` + `RegDecl` list) into a
`QCircuit n` term:

```
QASMProgram
    │
    ├── validate qubit count n
    │     (n = sum of register sizes)
    │
    ├── resolve QubitRefs to Fin n indices
    │     (reg name → offset, then + index within reg)
    │
    ├── convert GateApp → Gate n
    │     (single-qubit: index = global qubit index)
    │     (two-qubit: control and target indices)
    │
    └── emit QCircuit n via .cons/.empty
```

**Float → ℝ conversion (the angle recognizer):**

Rotation angles from QASM are `Float` values. The elaborator converts them to exact
`ℝ` expressions by matching against a 30+ case table of known rational multiples of π:

```
0.0          → 0
1.5707963... → Real.pi / 2
3.1415926... → Real.pi
0.7853981... → Real.pi / 4
...
```

Unrecognized angles produce a warning (`"unsupported angle: ..."`) and fall through to
a sorry stub. Structural proofs (gate count, depth) are unaffected because they
pattern-match on gate constructors, not angle values. Only measurement-probability
proofs fail for unrecognized angles.

**Well-formedness:**

The elaborator checks:
- All qubit indices are within bounds
- Two-qubit gates reference distinct qubits (control ≠ target)
- Register names are declared

The `checkWellFormed` function and its soundness theorem (`checkWellFormed_sound`)
are in `ParseTheorems.lean`.

### 8.3 Serializer (Serializer.lean)

`QCircuit n → String` emits valid OpenQASM 3. Used by `--emit-lean` to round-trip:

```
QASM input → parse → QCircuit n → serialize → QASM output
```

Round-trip is not an identity (angle expressions are simplified, register names are
normalized to `q`), but the semantics are preserved.

---

## 9. ZX-calculus

### 9.1 Diagram type (Diagram.lean)

```lean
inductive ZXDiagram : (m : ℕ) → (n : ℕ) → Type where
  | wire      : ZXDiagram 1 1
  | hadamard  : ZXDiagram 1 1
  | zSpider (m n : ℕ) (α : ℝ) : ZXDiagram m n
  | xSpider (m n : ℕ) (α : ℝ) : ZXDiagram m n
  | cap       : ZXDiagram 0 2
  | cup       : ZXDiagram 2 0
  | swap      : ZXDiagram 2 2
  | compose   : ZXDiagram m k → ZXDiagram k n → ZXDiagram m n
  | tensor    : ZXDiagram m₁ n₁ → ZXDiagram m₂ n₂ → ZXDiagram (m₁+m₂) (n₁+n₂)
```

The type `ZXDiagram m n` encodes wire counts at the type level. `compose d₁ d₂`
requires the output count of d₁ to match the input count of d₂ — verified at
elaboration time.

Notations:
- `d₁ ⊚ d₂` — sequential composition (d₁ first)
- `d₁ ↑⊗ d₂` — parallel tensor (d₁ on top)

### 9.2 Matrix semantics (Semantics.lean)

```lean
noncomputable def interpret : ZXDiagram m n →
    Matrix (Fin (2^n)) (Fin (2^m)) ℂ
```

Notation: `ZX⟦d⟧` = `interpret d`

The semantics maps:
- `wire` → 2×2 identity
- `hadamard` → `H_mat`
- `zSpider m n α` → a concrete matrix using `Complex.exp (I * α)`
- `xSpider m n α` → Hadamard conjugate of the Z-spider matrix
- `cap` → column vector `|00⟩ + |11⟩`
- `cup` → row vector `⟨00| + ⟨11|`
- `compose d₁ d₂` → `ZX⟦d₂⟧ * ZX⟦d₁⟧`
- `tensor d₁ d₂` → Kronecker product

### 9.3 Rewrite rules (Rules.lean)

Key proved theorems:

```lean
-- Z-spider fusion: composing two Z-spiders sums the phases
theorem zSpider_fusion (α β : ℝ) :
    ZX⟦zSpider α ⊚ zSpider β⟧ = ZX⟦zSpider (α + β)⟧

-- X-spider fusion (dual)
theorem xSpider_fusion (α β : ℝ) :
    ZX⟦xSpider α ⊚ xSpider β⟧ = ZX⟦xSpider (α + β)⟧

-- π-copy rule: a Z(π) spider copied through an X spider
theorem pi_copy : ZX⟦zSpider 2 1 π ⊚ xSpider 1 2 0⟧ =
                  ZX⟦xSpider 1 2 π ⊚ (zSpider 2 1 0 ↑⊗ zSpider 2 1 0)⟧
```

These correspond to the standard ZX-calculus equational theory.

### 9.4 Circuit translation (GateTranslation.lean)

```lean
-- Translate a standard 1-qubit gate to a ZX diagram
def gateToZX₁ (g : Gate 1) : ZXDiagram 1 1

-- Translate a 1-qubit circuit to a ZX diagram
def circuitToZX₁ (c : QCircuit 1) : ZXDiagram 1 1

-- Soundness: ZX semantics agree with circuit semantics
theorem gateToZX₁_sound (g : Gate 1) (hg : isStdGate₁ g) :
    ZX⟦gateToZX₁ g⟧ = g.matrix

theorem circuitToZX₁_sound (c : QCircuit 1) (hc : isStdCircuit₁ c) :
    ZX⟦circuitToZX₁ c⟧ = c.denote
```

`isStdGate₁` and `isStdCircuit₁` are decidable predicates that ensure the gate
or circuit only uses gates in the supported ZX translation (H, X, Y, Z, RZ).
The soundness proof goes by induction on the circuit structure.

---

## 10. Quantum Hoare Logic

### 10.1 Quantum predicates

```lean
structure QPred (n : ℕ) where
  mat : Matrix (Fin (2^n)) (Fin (2^n)) ℂ
  pos : matPSD mat              -- 0 ≤ mat (Löwner order)
  le1 : matPSD (1 - mat)        -- mat ≤ I
```

`matPSD M` = `M.IsHermitian ∧ ∀ x, 0 ≤ ⟨x, Mx⟩` (private definition).

The `pos` and `le1` fields enforce `0 ≤ A ≤ I` in the Löwner order. Externally,
only `QPred.trivial` (mat=0) and `QPred.full` (mat=I) are constructible without
going through the private `matPSD` definition. Custom predicates require direct
proofs of the PSD conditions.

### 10.2 Hoare triple

```lean
def HoareTriple {n : ℕ} (A : QPred n) (c : QCircuit n) (B : QPred n) : Prop :=
  ∀ ρ : DensityMatrix n,
    (A.mat * ρ.mat).trace.re ≤ (B.mat * (c.denote * ρ.mat * c.denote.conjTranspose)).trace.re
```

`tr(A·ρ) ≤ tr(B·c(ρ))` where `c(ρ) = c.denote · ρ · c.denote†`.

The expectation interpretation: `tr(A·ρ)` is the expected value of the observable A
in state ρ. The triple says: if A has expectation p before the circuit, B has
expectation ≥ p after.

### 10.3 Proof rules

```lean
-- Skip rule: empty circuit preserves any predicate
theorem hoare_skip (A : QPred n) : HoareTriple A .empty A

-- Gate rule: U†·A·U holds before → A holds after gate with unitary U
theorem hoare_gate (A : QPred n) (g : Gate n)
    (hU : g.matrix.conjTranspose * g.matrix = 1) :
    HoareTriple (A.conj g.matrix hU) (ofGate g) A

-- Sequential composition (requires c₁ is unitary)
theorem hoare_seq
    (hU₁ : c₁.denote.conjTranspose * c₁.denote = 1)
    (h₁  : HoareTriple A c₁ B) (h₂ : HoareTriple B c₂ C) :
    HoareTriple A (c₁ ++ c₂) C

-- Consequence rule: pre-weakening and post-weakening
theorem hoare_consequence
    (hA : matPSD (A.mat - A'.mat))   -- A' ≤ A
    (h  : HoareTriple A c B)
    (hB : matPSD (B'.mat - B.mat))   -- B ≤ B'
    : HoareTriple A' c B'
```

`QPred.conj U hU` computes the conjugate predicate `U† · A · U`.

The consequence rule weakens in both directions under the expectation interpretation:
larger A' (closer to 0) imposes less, and larger B' (closer to I) demands less.

---

## 11. Python bridge

### 11.1 Component roles

| File | Role |
|---|---|
| `bridge.py` | Top-level API: `verify_circuit`, `verify_circuit_spec` |
| `prover.py` | Structural spec proof generation and kernel-checking |
| `result.py` | `Verdict` enum, `VerifyResult` dataclass |
| `runner.py` | CLI entry point (`lean-qverify-build` console script) |
| `counterexample.py` | Qiskit Aer simulation for numerical counterexample search |
| `simulator.py` | CPU/GPU Aer backend selection |
| `gpu.py` | CUDA device detection; `GPU_QUBIT_THRESHOLD = 20` |

### 11.2 Verdict states

```python
class Verdict(Enum):
    PROVED        = "proved"       # Lean kernel checked a theorem against a spec
    STRUCT_PROVED = "struct_proved"# Structural spec kernel-checked (automated)
    PARSED        = "parsed"       # Circuit parsed; no spec checked
    FAILED        = "failed"       # Lean rejected, or counterexample found
    WARNING       = "warning"      # Parsed with unrecognised gates/angles
    ERROR         = "error"        # Could not parse / elaborate / run Lean
```

`result.ok` returns `True` for PROVED, STRUCT_PROVED, PARSED, WARNING.
`result.kernel_checked` returns `True` only for PROVED, STRUCT_PROVED.

### 11.3 verify_circuit flow

```
verify_circuit(qc, ...)
    │
    ├── _find_binary()          find lean-qverify-check on PATH / LEAN_QVERIFY_BIN
    │       │
    │       └── None → return Verdict.ERROR
    │
    ├── _circuit_to_qasm(qc)   qiskit.qasm3.dumps(qc)
    │
    ├── subprocess.run([check_bin, "--check", qasm_path])
    │       │
    │       ├── returncode != 0  → Verdict.ERROR
    │       ├── "not a recognised" in stdout → Verdict.WARNING
    │       └── ok               → parse n_qubits, n_gates from JSON output
    │
    └── return VerifyResult(verdict=PARSED, n_qubits=..., n_gates=...)
```

The `lean-qverify-check` binary parses the QASM and emits JSON:
```json
{"nQubits": 2, "nGates": 2, "warnings": []}
```

### 11.4 verify_circuit_spec flow (structural specs)

```
verify_circuit_spec(qc, spec, ...)
    │
    ├── guard spec is StructuralSpec
    │
    ├── _find_binary() → None → Verdict.ERROR (early check)
    │
    └── verify_structural_spec(qasm_source, spec)
            │
            ├── step 1: lean-qverify-check --emit-lean circuit.qasm
            │           → Lean definition string:
            │             "noncomputable def importedCircuit : QCircuit 2 := ..."
            │
            ├── step 2: _generate_theorem(circuit_lean, n_qubits, spec)
            │           → complete .lean file with theorem + proof
            │
            ├── step 3: write .lean to project root (so lake env can resolve imports)
            │
            ├── step 4: lake env lean temp_theorem.lean
            │
            └── step 5: returncode=0 and "error:" not in log.lower()
                        → proved=True → Verdict.STRUCT_PROVED
```

### 11.5 Generated theorem templates

**Gate count spec:**
```lean
theorem importedCircuit_spec :
    CircuitSpec.countGates (fun _ => true) importedCircuit = 2 :=
by
  simp [CircuitSpec.countGates, importedCircuit]
```

**Depth spec:**
```lean
theorem importedCircuit_spec :
    importedCircuit ⊨ CircuitSpec.maxDepth 2 :=
by
  simp [CircuitSpec.satisfies, CircuitSpec.depth,
        CircuitSpec.scheduleDepth, CircuitSpec.gateQubits,
        importedCircuit]
```

Both proofs rely on `simp` fully evaluating the concrete circuit. This works
because the circuit is a literal Lean term (not a symbolic variable).

### 11.6 Counterexample search

When a circuit does not satisfy a spec (or contains a `sorry` stub during
development), the bridge runs a numerical check:

```
DensityMatrix simulation via Qiskit Aer
    → sample a set of input states
    → for each: compute |output amplitudes|²
    → compare against spec bound
    → if violation found: return CounterExample(input_state, expected, actual)
```

GPU acceleration kicks in for circuits with ≥ 20 qubits when a CUDA device is
detected (`qiskit-aer-gpu`). Below that threshold, PCIe transfer overhead makes
GPU slower than CPU.

---

## 12. Build system

### 12.1 Main library (root)

`lakefile.lean` defines:
- Package `lean-qverify` (version 0.1.0.0)
- Dependency: Mathlib @ v4.33.0-rc1
- Library: `LeanQVerify` (root `LeanQVerify`)
- Executable: `lean-qverify-check` (root `LeanQVerify.Main`)
- Test library: `LeanQVerifyTests` (root `tests/lean`)

Build flow:
```bash
lake update          # resolve Mathlib, write lake-manifest.json
lake exe cache get   # download prebuilt Mathlib oleans (~500 MB)
lake build           # compile LeanQVerify + tests + binary
```

The `lean-toolchain` file pins to `leanprover/lean4:v4.33.0-rc1`. `elan` reads this
and switches to the correct toolchain automatically on directory entry.

### 12.2 Book (book/)

A separate Lake project that imports the main library as a git dependency.
`book/lakefile.lean` `require`s `lean-qverify` from the parent directory
(using a local path reference). The book builds against the compiled library
oleans — it does not recompile the library.

```bash
cd book
lake update        # resolves lean-qverify path dependency
lake exe cache get # Mathlib cache (already present from root build)
lake build         # compiles all 12 chapter modules
```

The PDF is built separately via a Python script (`make_book.py`, not committed)
that reads the chapter prose files and runs LuaLaTeX.

### 12.3 Theorems (theorems/)

A separate Lake project that imports `lean-qverify` from git at a pinned revision.
This is the independent verification artifact: it builds against a fixed
release of the library, proving all 38 core theorems again from scratch.

`theorems/lean-toolchain` pins to a different (older, stable) Lean version to
demonstrate that the theorem statements are not toolchain-specific.

### 12.4 Import graph

```
Mathlib
  └── LeanQVerify.Foundation.Unitary
        └── LeanQVerify.Circuit.Gate
              └── LeanQVerify.Circuit.QCircuit
                    ├── LeanQVerify.Circuit.Identities
                    ├── LeanQVerify.Circuit.Parametric
                    ├── LeanQVerify.Spec.CircuitSpec
                    │     ├── LeanQVerify.Spec.Satisfies
                    │     └── LeanQVerify.Spec.StandardSpecs
                    └── LeanQVerify.Foundation.HoareLogic
  └── LeanQVerify.Foundation.QState
        └── (used by StandardSpecs for measurement proofs)
  └── LeanQVerify.Foundation.DensityMatrix
        └── LeanQVerify.Foundation.HoareLogic
  └── LeanQVerify.ZX.Diagram
        └── LeanQVerify.ZX.Semantics
              └── LeanQVerify.ZX.Rules
                    └── LeanQVerify.ZX.GateTranslation
  └── LeanQVerify.QASM.Parser
        └── LeanQVerify.QASM.Elaborator
              └── LeanQVerify.QASM.ParseTheorems
                    └── LeanQVerify.QASM.Serializer
```

`LeanQVerify.lean` re-exports everything under a single import.

---

## 13. Invariants and design decisions

### D1: Qubit count in the type

`QCircuit n` and `Gate n` carry the qubit count `n` at the type level.
This means a Bell circuit is `QCircuit 2`, and a GHZ circuit is `QCircuit 3`.
They are different types — you cannot accidentally append a 2-qubit circuit to a
3-qubit circuit.

The trade-off: parametric theorems (e.g., "for all n, the identity circuit has n qubits")
require explicit universally-quantified `n` in the statement. Lean 4's elaborator
handles this smoothly with implicit arguments.

### D2: Gate angles are ℝ, not Float

QASM uses floating-point angles. The bridge converts them to exact real-number
expressions (e.g., `Real.pi / 2`). This is the only way `norm_num` can close goals
involving rotation angles — it works with algebraic expressions, not IEEE 754
approximations.

Unrecognized angles are a known limitation. They produce a warning and prevent
measurement-probability proofs. Gate-count and depth proofs are unaffected.

### D3: `noncomputable` is pervasive

Most matrix definitions and gate operations are `noncomputable` because they involve
`ℝ` and `ℂ`, which are not `Decidable` in Lean 4. This is expected in a library
built on real-number mathematics. It does not affect kernel verification —
`noncomputable` affects code generation, not proof checking.

Where computability matters (gate count, depth, well-formedness checking), the
definitions are kept computable by avoiding `ℝ` and using decidable types
(`ℕ`, `Bool`, `String`).

### D4: The parser is trusted

The QASM parser (`Parser.lean`, `Elaborator.lean`) is not formally verified. It is
explicitly marked as a trusted bridge component. The chain of trust for a Lane A
result is: Qiskit → QASM string → parser → QCircuit n → theorem → Lean kernel.
If the parser has a bug (wrong gate, wrong index), the theorem will be about a
different circuit than intended.

Mitigation: `checkWellFormed_sound` in `ParseTheorems.lean` proves that the
well-formedness checker correctly identifies valid programs. Concrete Bell and GHZ
circuits are unit-tested with `by rfl`.

### D5: applyUnitary requires explicit unitarity proof

```lean
def applyUnitary (ρ : DensityMatrix n) (U : ...) (hU : U† * U = 1) : DensityMatrix n
```

The caller must supply a proof that U is unitary. This prevents applying an
arbitrary matrix to a density matrix (which would break the trace-1 and PSD
invariants). Gate unitarity is proved once per gate type and reused.

### D6: QASM elaboration uses a flat qubit index

All qubit registers are flattened into a single `Fin n` index by accumulating
register offsets. A QASM program with `qubit[2] q; qubit[1] r;` maps `q[0]→0`,
`q[1]→1`, `r[0]→2`. This matches how most QASM circuits are structured in practice
(single register, or a few registers with fixed names).

### D7: Book chapter theorems are separate from the main library

The book lives in `book/`, a separate Lake project. Its Lean examples are real
theorems that are kernel-checked as part of `lake build Book`, but they are not
counted in the main library's theorem list. They are extra examples on top of the
38 core theorems in `LeanQVerify/` and `theorems/`.

---

*Last updated: v0.1.0.0*
