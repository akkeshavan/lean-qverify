# lean-qverify

Formal verification of quantum circuits, connecting Qiskit to Lean 4 + Mathlib.

Write a quantum circuit in Qiskit, export it to OpenQASM 3, and have Lean's proof kernel verify it satisfies a formal specification — or get a concrete numerical counterexample when it doesn't.

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

## Proved theorems

All of the following are kernel-checked — no `sorry` anywhere in the proof tree:

| Circuit | Property | Proof tactic |
|---|---|---|
| Bell prep | gate count = 2, CNOT count = 1 | `simp` |
| Bell prep | depth ≤ 2 | `simp` |
| Bell prep | P(q₀=0) = ½, P(q₀=1) = ½ | explicit matrix + `norm_num` |
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
| Grover (2-qubit, 1 step) | P(q₀=1) ≥ 0.99 | explicit 4×4 unitary + `norm_num` |

All 24 theorems are kernel-checked with no `sorry` in the proof tree.

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
│   │   └── Identities.lean     -- proved gate identity theorems
│   ├── Spec/
│   │   ├── CircuitSpec.lean    -- specification language and ⊨ relation
│   │   ├── Satisfies.lean      -- satisfaction lemmas (monotonicity etc.)
│   │   └── StandardSpecs.lean  -- Bell, GHZ, teleportation, HEA, Grover
│   └── QASM/
│       ├── Parser.lean         -- OpenQASM 3 recursive-descent parser
│       └── Elaborator.lean     -- AST → ElabResult / QCircuit n
├── lean_qverify/               -- Python bridge package
│   ├── bridge.py               -- Qiskit → lean-qverify-check integration
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
├── lean-toolchain              -- pins Lean 4.14.0
└── pyproject.toml              -- Python package config
```

---

## Setup

### Prerequisites

| Tool | Version | Install |
|---|---|---|
| Lean 4 | 4.14.0 (pinned via `lean-toolchain`) | [elan](https://github.com/leanprover/elan) |
| Mathlib | 4.14.0 | fetched automatically by `lake` |
| Python | ≥ 3.10 | system or conda |
| Qiskit | ≥ 1.0 | `pip install qiskit` |

### 1. Install Lean via elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your shell, then verify:

```bash
lean --version   # should print Lean 4.14.0
lake --version
```

### 2. Clone and build

```bash
git clone https://github.com/akkeshavan/lean-qverify
cd lean-qverify

# Fetch Mathlib (first run downloads ~500 MB of prebuilt cache)
lake update

# Build the verifier binary and all library files
lake build
```

The verifier binary lands at `.lake/build/bin/lean-qverify-check`.

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

**Complete.** All core types, parser, elaborator, specification language, and 24 kernel-checked theorems are implemented and building with no `sorry` remaining.

See `SPEC.md` for the full design specification and `FUTURE_WORK.md` for the roadmap.
