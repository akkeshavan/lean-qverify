# lean-qverify

Formal verification of quantum circuits, connecting Qiskit to Lean 4 + Mathlib.

Write a quantum circuit in Qiskit, export it to OpenQASM 3, and have Lean's proof kernel verify it satisfies a formal specification — or get a concrete numerical counterexample when it doesn't.

**Two components, two directories:**

| Directory | Language | What it is |
|---|---|---|
| `LeanQVerify/` | Lean 4 | The formal library: gate types, circuit semantics, specification language, proved theorems, QASM parser, ZX-calculus, Hoare logic. Import this in your Lean projects. |
| `lean_qverify/` | Python | The bridge package: exports Qiskit circuits to QASM, calls the compiled `lean-qverify-check` binary, parses results, runs counterexample search. Install via `pip`. |

They are independent. The Python package shells out to a binary built from the Lean library — it does not import Lean code directly. The naming follows each language's convention (PascalCase for Lean modules, snake_case for Python packages).

---

## The approach

Quantum programs are hard to test. A misplaced CNOT or a rotation angle off by a factor of two produces subtly wrong measurement statistics rather than a crash. Classical simulation can check specific inputs but cannot prove correctness for all inputs, and beyond ~50 qubits it is not even feasible.

**Formal verification** provides a different guarantee: a machine-checked proof that the circuit's unitary matrix satisfies a stated property for *all* inputs, regardless of qubit count or noise model.

This library connects the two worlds:

```
Qiskit (Python)        →   lean-qverify   →   Lean 4 proof kernel
QuantumCircuit             OpenQASM 3          QCircuit n / CircuitSpec
(practitioner tool)        (interchange)       (kernel-checked theorem)
```

### How it works

1. **Export.** Any Qiskit `QuantumCircuit` is exported to OpenQASM 3 via `qiskit.qasm3.dumps`.

2. **Parse & elaborate.** A Lean 4 recursive-descent parser converts the QASM text into a typed `QCircuit n` value, where the qubit count `n` is encoded in the type. Out-of-bounds qubit indices are impossible by construction.

3. **Specify.** A first-order specification language `CircuitSpec n` lets you state properties:
   - `implementsMatrix U` — the circuit's unitary equals U
   - `equivalentTo c'` — two circuits implement the same unitary
   - `measurementProb ψ i b p` — measuring qubit `i` starting from state `ψ` gives outcome `b` with probability ≥ p
   - `gateCount pred k` — at most k gates matching a predicate
   - `maxDepth k` — parallel depth at most k
   - `both s₁ s₂` — conjunction

4. **Prove.** Lean's kernel checks the proof. Simple specs (`simp` closes gate-count and depth goals automatically). Measurement-probability proofs expand the matrix explicitly and close with `norm_num`.

5. **Counterexample search.** When a proof contains a `sorry` stub during development, the Python bridge runs the circuit through Qiskit Aer (CPU or GPU) and searches for a concrete input state that violates the spec.

### Two lanes

```
LANE A — automated check (Python bridge + lean-qverify-check binary)

  Qiskit QuantumCircuit
       │  qiskit.qasm3.dumps()
       ▼
  OpenQASM 3 string
       │  Parser.lean
       ▼
  QASMProgram (untyped AST)
       │  Elaborator.lean
       ▼
  ElabResult { nQubits, nGates, warnings }   →   JSON output
       │
  [on warnings or spec failure]
  Python bridge  →  Qiskit Aer (CPU or GPU)  →  counterexample state


LANE B — formal proof (developer writes Lean theorems)

  QCircuit n  (same value as Lane A)
       │  c ⊨ s  (satisfies relation)
       ▼
  Prop  ──  lake build  ──►  kernel-checked proof
```

Lane A gives fast automated feedback. Lane B gives a kernel-checked guarantee. Only Lane B is a formal proof.

---

## Artifact evaluation

To independently verify all 40 proved theorems, see
**[`theorems/README.md`](theorems/README.md)** for step-by-step build
instructions, expected output, and a sorry audit.

---

## Proved theorems

All of the following are kernel-checked — no `sorry` anywhere in the proof tree:

**Structural and equivalence theorems** (automated via `simp`):

| Circuit | Property | Proof tactic |
|---|---|---|
| Bell prep | gate count = 2, CNOT count = 1 | `simp` |
| Bell prep | depth ≤ 2 | `simp` |
| GHZ prep | gate count = 3, depth ≤ 3 | `simp` |
| Teleportation | pre-measurement depth ≤ 4 | `simp` |
| HEA (4-qubit) | 7 gates, 3 CNOTs, 4 RZ, depth ≤ 4 | `simp` |
| HEA (4-qubit) | RZ(0) layer ≡ bare CNOT chain | `Rz_zero_id` |
| H∘H, X∘X, Y∘Y, Z∘Z | ≡ I | `embedGate1_self_inverse` |
| CNOT∘CNOT | ≡ I | `embedCNOT_self_mul` |
| H∘X∘H, H∘Z∘H | ≡ Z, ≡ X | `nlinarith` |
| RZ(0) | ≡ I | `Rz_zero_id` |
| RZ(θ)∘RZ(φ) | ≡ RZ(θ+φ) | `Rz_mat_add` |
| SWAP | ≡ CNOT(i,j)∘CNOT(j,i)∘CNOT(i,j) | `Nat.testBit_xor` + sum collapse |

**Semantic theorems** (automated via `verify_prob`):

| Circuit | Property | Backend |
|---|---|---|
| Bell prep | P(q₀=0) = ½, P(q₀=1) = ½ | dense evaluator |
| Bell prep | joint P(|00⟩) ≥ ½, joint P(|11⟩) ≥ ½ | dense evaluator |
| GHZ (3-qubit) | joint P(|000⟩) ≥ ½, joint P(|111⟩) ≥ ½ | dense evaluator |
| Grover (2-qubit, 1 step) | P(q₀=1) ≥ 0.99 | dense evaluator |
| RZ(π) on \|0⟩ | P(q₀=0) = 1 | dense evaluator + `Rz_mat_pi` |
| Bell prep (Clifford form) | P(q₀=0) = ½ | stabilizer tableau (O(n²)) |
| GHZ (100-qubit) | P(q₀=0) = ½ | stabilizer tableau (O(n²)) |

All 40 theorems are kernel-checked with no `sorry` in the proof tree.
The core 38 are independently verifiable via the `theorems/` folder; 2 additional theorems are in the book examples (Chapters 11–12).

---

## Repository layout

```
lean-qverify/
├── LeanQVerify/
│   ├── Foundation/
│   │   ├── QState.lean         -- normalised state vectors and basis states
│   │   ├── Unitary.lean        -- gate matrices and embedding into 2^n space
│   │   └── DensityMatrix.lean  -- density matrix formalism (infrastructure)
│   ├── Circuit/
│   │   ├── Gate.lean           -- Gate n inductive type and matrices
│   │   ├── QCircuit.lean       -- circuit datatype, denotational semantics
│   │   ├── Identities.lean     -- proved gate identity theorems
│   │   └── Parametric.lean     -- parametric circuit families (ghzCircuit n)
│   ├── Spec/
│   │   ├── CircuitSpec.lean    -- specification language and ⊨ relation
│   │   ├── Satisfies.lean      -- satisfaction lemmas (monotonicity etc.)
│   │   └── StandardSpecs.lean  -- Bell, GHZ, teleportation, HEA, Grover
│   ├── Stabilizer/
│   │   ├── CliffordGate.lean   -- CliffordGate, CliffordCircuit, Clifford classifier
│   │   ├── PauliGroup.lean     -- Pauli group; Clifford conjugation lemmas
│   │   ├── StabTableau.lean    -- Aaronson–Gottesman 2n-row tableau; stepH/S/CNOT
│   │   └── Sound.lean          -- Represents, stabSim_correct, zProb_correct, soundness
│   ├── Tactic/
│   │   ├── EvalCircuit.lean    -- gate-by-gate symbolic evaluator (avoids 2^n matrix)
│   │   └── VerifyProb.lean     -- verify_prob tactic; verify_clifford Clifford dispatch
│   └── QASM/
│       ├── Parser.lean         -- OpenQASM 3 recursive-descent parser
│       └── Elaborator.lean     -- AST → ElabResult / QCircuit n
├── book/
│   ├── Book/Ch01–Ch12/         -- Lean examples for each chapter
│   ├── book.pdf                -- compiled book (12 chapters, ~50 pages)
│   └── README.md               -- book build instructions
├── lean_qverify/               -- Python bridge package
│   ├── bridge.py               -- Qiskit → lean-qverify-check integration
│   ├── prover.py               -- structural spec proof pipeline
│   ├── gpu.py                  -- GPU detection and fallback
│   ├── simulator.py            -- Aer simulator selector
│   ├── counterexample.py       -- numerical counterexample search
│   ├── result.py               -- VerifyResult datatype
│   └── runner.py               -- CLI entry point
├── tests/
│   ├── circuits/               -- .qasm test circuits
│   ├── lean/                   -- Lean unit tests (TestParser, TestCircuit, …)
│   └── python/                 -- pytest suite for the Python bridge
├── examples/
│   ├── bell_state.py
│   ├── teleportation.py
│   └── grover_verify.py
├── lakefile.lean               -- Lean build config
├── lean-toolchain              -- pins Lean 4.33.0-rc1
└── pyproject.toml              -- Python package config
```

---

## Using as a Lean library

Add `lean-qverify` to your project's `lakefile.lean`:

```lean
require «lean-qverify» from git
  "https://github.com/akkeshavan/lean-qverify" @ "v0.1.0.0"
```

Then in your Lean files:

```lean
import LeanQVerify

open LeanQVerify

-- A 2-qubit Bell-state preparation circuit
#check QCircuit.bellPrep   -- QCircuit 2

-- Verify it has exactly 2 gates
example : QCircuit.bellPrep ⊨ CircuitSpec.totalGates 2 := by
  simp [CircuitSpec.satisfies, CircuitSpec.countGates, QCircuit.bellPrep,
        CircuitSpec.totalGates]
```

---

## Setup (development)

### Prerequisites

| Tool | Version | Install |
|---|---|---|
| Lean 4 | 4.33.0-rc1 (pinned via `lean-toolchain`) | [elan](https://github.com/leanprover/elan) |
| Mathlib | 4.33.0-rc1 | fetched automatically by `lake` |
| Python | ≥ 3.10 | system or conda |
| Qiskit | ≥ 1.0 | `pip install qiskit` |

### 1. Install Lean via elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### 2. Build

```bash
# From inside the lean-qverify directory:

# Fetch Mathlib and lock dependency versions
lake update

# Download prebuilt Mathlib oleans (saves ~30 min of compilation)
lake exe cache get

# Build everything
lake build
```

The CLI binary lands at `.lake/build/bin/lean-qverify-check`.

### 3. Install the Python package

```bash
pip install -e .

# GPU support (Linux + NVIDIA CUDA 12 only):
pip install -e ".[gpu]"
```

---

## Running the tests

### Lean tests

The Lean test suite covers the parser, elaborator, circuit specs, and quantum state proofs. All tests run at elaboration time — any failure is a build error.

```bash
# Run all four test modules
lake build LeanQVerifyTests

# Or build a specific module
lake build TestParser
lake build TestCircuit
lake build TestQState
lake build TestElaborator
```

A clean build with no errors means all `#guard` assertions and `example` proofs passed.

### Python tests

```bash
pytest tests/python/

# Skip GPU tests on machines without NVIDIA hardware
pytest tests/python/ -m "not gpu"
```

### Check a QASM file directly

```bash
.lake/build/bin/lean-qverify-check tests/circuits/bell.qasm
# → {"nQubits":2,"nGates":2,"warnings":[]}
```

---

## Usage

### From Python (Qiskit)

```python
from qiskit import QuantumCircuit
from lean_qverify import verify_circuit

qc = QuantumCircuit(2)
qc.h(0)
qc.cx(0, 1)

result = verify_circuit(qc)
print(result)
# VerifyResult(status='parsed', nQubits=2, nGates=2, warnings=[])
```

### Writing a Lean spec

```lean
import LeanQVerify.Spec.StandardSpecs

open LeanQVerify QCircuit CircuitSpec

-- Prove that Bell prep uses exactly 2 gates
theorem myCircuit_twoGates :
    bellPrep ⊨ .gateCount (fun _ => true) 2 := by
  simp [satisfies, countGates, bellPrep]

-- Prove measurement probability
theorem myCircuit_entangled :
    bellPrep ⊨ .measurementProb QState.ket00 0 false (1/2) :=
  bellPrep_entangled   -- already proved in StandardSpecs
```

---

## GPU counterexample search

GPU acceleration is used automatically for circuits with ≥ 20 qubits when a CUDA device is detected. Below that threshold the CPU statevector simulator is faster due to PCIe transfer overhead.

| Platform | Backend |
|---|---|
| Linux + NVIDIA | GPU (`qiskit-aer-gpu`) |
| macOS (Apple Silicon) | CPU (CUDA not supported) |
| Any other | CPU (`qiskit-aer`) |

Install with `pip install -e ".[gpu]"` on a CUDA 12 machine. The package falls back to CPU silently if no GPU is found.

---

## Status

**v0.1.0.0.** All core types, parser, elaborator, specification language, and 40 kernel-checked theorems are implemented. The `verify_prob` tactic automates measurement-probability proofs: it dispatches Clifford circuits to a verified Aaronson–Gottesman stabilizer tableau backend (O(n²) per gate, handles 100+ qubits) and falls back to a dense gate-by-gate evaluator for small circuits. One infrastructure stub remains in `DensityMatrix.lean` (post-measurement state collapse) — it is unused by any proved theorem. See the sorry audit in `theorems/README.md`.

See `SPEC.md` for the full design specification and `SEMANTIC_ROADMAP.md` for the automation roadmap.
