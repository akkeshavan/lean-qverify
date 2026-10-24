# lean-qverify — Design Specification

**Status: v3 — 40 kernel-checked theorems; ZX-calculus with certified circuit translation; genuine end-to-end structural verification pipeline; 32-circuit benchmark suite; targeting CAV 2027 (deadline Jan 20, 2027).** This document reflects the implemented system.

---

## 1. Problem statement

Quantum programs cannot be debugged the way classical programs can. Measuring a qubit mid-computation destroys its state. Results are probabilistic. There is no step-through debugger for quantum state.

Testing helps but is insufficient: you can check statistical distributions, but you cannot exhaustively verify correctness, and on real hardware, noise makes it impossible to distinguish a correct program from a slightly wrong one without a reference to compare against.

Formal verification sidesteps testing entirely. It proves mathematically — without running the program — that a circuit satisfies a specification. This project builds the infrastructure to do that for programs written in Qiskit, the most widely used quantum SDK.

---

## 2. Goals

- Provide a Lean 4 library with rigorous mathematical semantics for quantum circuits
- Allow developers to state and prove correctness properties about their Qiskit circuits
- Support equivalence checking between two circuits (e.g., original vs. optimised)
- Support probabilistic specifications (e.g., "this circuit finds the answer with probability ≥ 0.99")
- Support gate-count and depth specifications (structural, proved by `simp`)
- Target publication at CAV 2027

### Non-goals (v1)

- Full formal verification of noise models or decoherence
- Verification of PennyLane parameterised circuits
- Hardware-level transpilation correctness beyond gate semantics
- A complete OpenQASM 3 parser (a practical subset is sufficient)
- Support for qudits (d > 2)

---

## 3. Architecture

```
LANE A — automated parse + counterexample search

  Qiskit QuantumCircuit
       │  qiskit.qasm3.dumps() / OpenQASM 2.0 preprocessor
       ▼
  QASM source (v2 or v3)
       │  LeanQVerify.QASM.Parser
       ▼
  QASMProgram (untyped AST)
       │  LeanQVerify.QASM.Elaborator
       ▼
  ElabResult { nQubits, nGates, warnings }   ← Verdict.PARSED
       │
  [on warnings/failures]
  Python bridge  →  Qiskit Aer (CPU or GPU)  →  counterexample state


LANE B — formal proof of hand-written theorems

  QCircuit n
       │  c ⊨ s  (CircuitSpec.satisfies)
       ▼
  Prop  ─  lake build  ─►  kernel-checked   ← Verdict.PROVED


LANE C — end-to-end structural verification of imported circuits

  QASM source
       │  lean-qverify-check --emit-lean
       ▼
  Lean noncomputable def importedCircuit : QCircuit n
       │  _generate_theorem()  [Python]
       ▼
  theorem importedCircuit_spec :
      importedCircuit ⊨ .gateCount pred k  /  .maxDepth k
  := by simp [countGates, importedCircuit]
       │  lake env lean <tempfile>
       ▼
  kernel-checked proof                       ← Verdict.STRUCT_PROVED
```

GPU acceleration applies only to Lane A (Python tooling). The Lean proof kernel is always CPU-only.

---

## 4. Component 1: Mathematical foundation

**Location:** `LeanQVerify/Foundation/`

### QState (`QState.lean`)

An n-qubit pure state is a unit vector in `ℂ^(2^n)`:

```lean
def QState (n : ℕ) :=
  { v : Fin (2^n) → ℂ // ∑ i, Complex.normSq (v i) = 1 }
```

Standard basis states implemented: `ket0`, `ket1`, `ket00`, `ket01`, `ket10`, `ket11`, `ketPlus`, `ketMinus`, `bellPhi`.

### Gate matrices (`Unitary.lean`)

Each gate has a concrete matrix in `ℂ`. Key functions:

```lean
-- Embed a 2×2 matrix acting on qubit i into the 2^n × 2^n space
def embedGate1 (n : ℕ) (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ

-- Embed CNOT(control, target) into 2^n × 2^n space
def embedCNOT (n : ℕ) (c t : Fin n) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ
```

Both use `Nat.testBit` for flat qubit indexing, avoiding tensor product coherence issues.

Key lemmas proved: `embedGate1_mul` (composition), `embedGate1_self_inverse` (self-inverse gates), `embedGate1_one` (identity embedding), `embedCNOT_self_mul` (CNOT self-inverse), `Rz_zero_id`, `Rz_mat_add`.

### DensityMatrix (`DensityMatrix.lean`)

Infrastructure for mixed states. `DensityMatrix n` is a Hermitian, positive-semidefinite, unit-trace matrix.

**All proofs are complete** (no `sorry` stubs in `ofPure` or `applyUnitary`):
- `ofPure ψ` — inline proofs of `hermitian` (conjugate symmetry via `conjSwap`), `pos_sdef` (via Cauchy-Schwarz), `trace_one` (via ψ's unit-norm condition)
- `applyUnitary U hU ρ` — inline proofs that unitarily transformed density matrices remain Hermitian, PSD, and trace-1
- `measure` — intentional `sorry` stub (not yet used by any proved theorem; measurement collapse requires classical communication modelling out of scope for v2)

---

## 5. Component 2: Circuit type and semantics

**Location:** `LeanQVerify/Circuit/`

### Gate type (`Gate.lean`)

```lean
inductive Gate (n : ℕ) : Type where
  | H    : Fin n → Gate n
  | X    : Fin n → Gate n
  | Y    : Fin n → Gate n
  | Z    : Fin n → Gate n
  | S    : Fin n → Gate n
  | T    : Fin n → Gate n
  | RX   : ℝ → Fin n → Gate n
  | RY   : ℝ → Fin n → Gate n
  | RZ   : ℝ → Fin n → Gate n
  | CNOT : Fin n → Fin n → Gate n
  | CZ   : Fin n → Fin n → Gate n
  | SWAP : Fin n → Fin n → Gate n
  | CCX  : Fin n → Fin n → Fin n → Gate n
```

Qubit indices are `Fin n` — out-of-bounds references are impossible at the type level. Rotation angles are `ℝ` — float/radian confusion is ruled out.

`Gate.matrix : Gate n → Matrix (Fin (2^n)) (Fin (2^n)) ℂ` gives the 2^n × 2^n unitary for each gate via `embedGate1` or `embedCNOT`.

### Circuit type and semantics (`QCircuit.lean`)

```lean
inductive QCircuit (n : ℕ) : Type where
  | empty : QCircuit n
  | cons  : Gate n → QCircuit n → QCircuit n

-- Sequential composition: run c₁ first, then c₂
def append : QCircuit n → QCircuit n → QCircuit n

-- Denotational semantics
noncomputable def denote : QCircuit n →
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ
  | .empty    => 1
  | .cons g c => c.denote * g.matrix
```

`cons g c` means gate `g` is applied first. In matrix notation, `denote (cons g c) = denote c * matrix g`, reading right-to-left as in the standard circuit diagram convention.

Key theorem:
```lean
theorem denote_append (c₁ c₂ : QCircuit n) :
    (c₁ ++ c₂).denote = c₂.denote * c₁.denote
```

Standard named circuits: `bellPrep`, `ghzPrep` (in `QCircuit.lean`); `teleportPrep`, `groverOracle2`, `groverDiffusion2`, `groverStep2`, `hea4` (in `StandardSpecs.lean`).

### Parametric circuit families (`Parametric.lean`)

```lean
-- Embed a circuit for n qubits into one for n+1 qubits (new qubit unused)
def QCircuit.castSucc {n} : QCircuit n → QCircuit (n + 1)

-- A family of circuits indexed by ℕ, with qubit count f(n)
def QFamily (f : ℕ → ℕ) := (n : ℕ) → QCircuit (f n)

-- GHZ state preparation: H on qubit 0, then CNOT(0,k) for k=1..n
def ghzCircuit : (n : ℕ) → QCircuit (n + 1)
def ghzFamily  : QFamily (· + 1) := ghzCircuit

-- Bernstein-Vazirani oracle: CNOT(i,n) for each i where s[i] = true
def bvOracle (n : ℕ) (s : Fin n → Bool) : QCircuit (n + 1)
def bvCircuit (n : ℕ) (s : Fin n → Bool) : QCircuit (n + 1)
def bvFamily  (s : (n : ℕ) → Fin n → Bool) : QFamily (· + 1)
```

Key theorems proved by structural induction:
- `countGates_append` — gate count is additive over circuit composition
- `ghzCircuit_gateCount n` — GHZ for n+1 qubits has exactly n+1 gates
- `ghzCircuit_cnotCount n` — GHZ for n+1 qubits has exactly n CNOT gates
- `bvOracle_cnotCount_le n s` — BV oracle uses at most n CNOT gates

Proof technique: `show` tactic exploits that `cnotPred (.CNOT ..)` and `cnotPred (.H ..)` reduce definitionally, bypassing `if_true`/`if_false` simp lemma issues; `castSucc_countCNOT` tracks the CNOT count through the `castSucc` embedding.

### Circuit equivalence

```lean
def equiv (c₁ c₂ : QCircuit n) : Prop :=
  c₁.denote = c₂.denote

notation:50 c₁ " ≅ " c₂ => QCircuit.equiv c₁ c₂
```

### Proved gate identities (`Identities.lean`)

| Theorem | Status |
|---|---|
| `H_H_eq_id` — H∘H ≅ I | ✓ proved |
| `X_X_eq_id` — X∘X ≅ I | ✓ proved |
| `Y_Y_eq_id` — Y∘Y ≅ I | ✓ proved |
| `Z_Z_eq_id` — Z∘Z ≅ I | ✓ proved |
| `CNOT_CNOT_eq_id` — CNOT∘CNOT ≅ I | ✓ proved |
| `H_X_H_eq_Z` — H∘X∘H ≅ Z | ✓ proved |
| `H_Z_H_eq_X` — H∘Z∘H ≅ X | ✓ proved |
| `RZ_zero_eq_id` — RZ(0) ≅ I | ✓ proved |
| `RZ_add` — RZ(θ)∘RZ(φ) ≅ RZ(θ+φ) | ✓ proved |
| `SWAP_eq_three_CNOTs` — SWAP ≅ CNOT³ | ✓ proved — `Nat.testBit_xor` + sum collapse |

---

## 6. Component 3: Specification language

**Location:** `LeanQVerify/Spec/`

### CircuitSpec (`CircuitSpec.lean`)

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

`jointMeasProb ψ bs p` states: starting from input state ψ, measuring all n qubits and observing basis state bs (encoded as a `Fin (2^n)` index) happens with probability ≥ p. This captures joint multi-qubit distributions (unlike `measurementProb` which is a single-qubit marginal). Satisfaction: `p ≤ Complex.normSq ((c.applyTo ψ.val) bs)`.

Convenience aliases: `isIdentity`, `isBellPrep`, `totalGates`, `maxCNOTs`.

### Satisfaction relation

```lean
noncomputable def satisfies (c : QCircuit n) : CircuitSpec n → Prop
  | .implementsMatrix U       => c.denote = U
  | .equivalentTo c'          => c ≅ c'
  | .measurementProb ψ i b p  => p ≤ measProb c ψ i b
  | .gateCount pred k         => countGates pred c ≤ k
  | .maxDepth k               => depth c ≤ k
  | .both s₁ s₂               => satisfies c s₁ ∧ satisfies c s₂

notation:40 c " ⊨ " s => CircuitSpec.satisfies c s
```

`measProb` computes measurement probability by summing `Complex.normSq` of amplitudes for basis states where the target bit matches the expected outcome. It does not use the DensityMatrix infrastructure.

`depth` uses a list-scheduling algorithm: `scheduleDepth` tracks per-qubit earliest-available times; `gateQubits` maps each gate to its qubit set.

`countGates pred c` counts gates in `c` satisfying predicate `pred`.

### Satisfaction lemmas (`Satisfies.lean`)

- `empty_satisfies_identity` — empty circuit satisfies identity spec
- `satisfies_both`, `satisfies_both_left`, `satisfies_both_right` — conjunction rules
- `equiv_imp_sameMatrix`, `satisfies_equiv_iff` — equivalence and matrix specs
- `satisfies_gateCount_mono` — monotonicity: if `c ⊨ .gateCount pred k` and `k ≤ k'` then `c ⊨ .gateCount pred k'`
- `ofGate_gateCount_self`, `empty_gateCount_zero` — single-gate and empty circuits

### Standard specs (`StandardSpecs.lean`)

| Theorem | Spec | Status |
|---|---|---|
| `bellPrep_twoGates` | gate count = 2 | ✓ simp |
| `bellPrep_oneCNOT` | CNOT count = 1 | ✓ simp |
| `bellPrep_depth` | depth ≤ 2 | ✓ simp |
| `bellPrep_entangled` | P(q₀=0) = ½ | ✓ matrix + norm_num |
| `bellPrep_entangled_one` | P(q₀=1) = ½ | ✓ matrix + norm_num |
| `ghzPrep_threeGates` | gate count = 3 | ✓ simp |
| `ghzPrep_depth` | depth ≤ 3 | ✓ simp |
| `teleportPrep_depth` | depth ≤ 4 | ✓ simp |
| `hea4_gateCount` | gate count = 7 | ✓ simp |
| `hea4_cnotCount` | CNOT count = 3 | ✓ simp |
| `hea4_rzCount` | RZ count = 4 | ✓ simp |
| `hea4_depth` | depth ≤ 4 | ✓ simp |
| `hea4_zero_eq_cnotChain` | hea4(0,0,0,0) ≅ cnotChain | ✓ Rz_zero_id |
| `hea4_rz_fuse_single` | RZ(θ)∘RZ(φ) ≅ RZ(θ+φ) | ✓ Rz_mat_add |
| `groverStep2_correct` | P(q₀=1) ≥ 0.99 | ✓ proved — 4×4 unitary + `norm_num` |
| `bellPrep_joint_ket00` | P(|00⟩) ≥ 1/2 | ✓ jointMeasProb + norm_num |
| `bellPrep_joint_ket11` | P(|11⟩) ≥ 1/2 | ✓ jointMeasProb + norm_num |
| `bellPrep_joint_ket01_zero` | P(|01⟩) = 0 | ✓ jointMeasProb + norm_num |
| `bellPrep_joint_ket10_zero` | P(|10⟩) = 0 | ✓ jointMeasProb + norm_num |

---

## 7. Component 4: QASM bridge

**Location:** `LeanQVerify/QASM/` (Lean) + `lean_qverify/` (Python)

### Parser (`Parser.lean`)

A recursive-descent parser over `String`. Produces a `QASMProgram`:

```lean
structure QASMProgram where
  registers : List RegDecl     -- qubit[n] name declarations
  gates     : List GateApp     -- gate applications
  warnings  : List String      -- unsupported constructs skipped

structure RegDecl where
  name : String
  size : ℕ

inductive GateApp : Type where
  | h | x | y | z | s | t : QubitRef → GateApp
  | rx | ry | rz : Float → QubitRef → GateApp
  | cx | cz | swap : QubitRef → QubitRef → GateApp
  | ccx : QubitRef → QubitRef → QubitRef → GateApp
  | skipped : String → GateApp
```

Supported (OpenQASM 3): `OPENQASM 3;`, `include "stdgates.inc"` (skipped), `qubit[n] name;`, `bit`/`creg` (ignored), all standard gates, rotation gates with angles (`pi`, `pi/N`, `pi*N`, decimals, negatives, scientific notation `1.2e-3`), line comments `//`.

Supported (OpenQASM 2.0): `OPENQASM 2.0;`, `include "qelib1.inc"` (skipped), `qreg name[n];`, `creg`/`measure`/`barrier` (ignored), `sdg`/`tdg` (mapped to `RZ(−π/2)`, `RZ(−π/4)`), `u1`/`p` phase gates (mapped to `RZ`), `toffoli` (alias for `ccx`), `id` (dropped as no-op).

Unsupported constructs (e.g. `u2`, `u3`, custom gate definitions) produce a `.skipped` warning rather than failing.

The parser is a trusted component at the gate-application level. A formal well-formedness specification is provided in `ParseTheorems.lean`:

```lean
-- Extract all qubit references from a parsed gate (22 constructors)
def GateApp.qubitRefs (g : GateApp) : List QubitRef

-- Formal Prop: every gate's qubit refs are within the declared register bounds
def GateApp.wellFormedFor (regs : List RegDecl) (g : GateApp) : Prop
def QASMProgram.wellFormed (prog : QASMProgram) : Prop

-- Computable Bool checker
def checkGateWF (regs : List RegDecl) (g : GateApp) : Bool
def QASMProgram.checkWellFormed (prog : QASMProgram) : Bool

-- Soundness: checker implies formal predicate (kernel-checked)
theorem checkWellFormed_sound {prog} (h : prog.checkWellFormed = true) : prog.wellFormed
```

Concrete theorems: Bell program well-formed (`by rfl`), GHZ-3 program well-formed (`by rfl`), out-of-bounds program fails checker (`by rfl`). Proofs are about the `QCircuit n` value it produces.

### Elaborator (`Elaborator.lean`)

Two-phase elaboration with different computability requirements:

**Phase 1 — computable (for the CLI):**
```lean
structure ElabResult where
  nQubits  : Nat
  nGates   : Nat
  warnings : List String

def elaborate (prog : QASMProgram) : ElabResult
def parseAndElaborate (source : String) : ElabResult
```

**Phase 2 — noncomputable (for proofs):**
```lean
noncomputable def elaborateCircuit (prog : QASMProgram) :
    Σ n : Nat, QCircuit n
```

The split is necessary because `RX`/`RY`/`RZ` gates take `ℝ` angles, which is noncomputable in Lean. The Float→ℝ conversion in Phase 2 uses a 30+ case if-chain recognizing rational-π multiples (`floatToReal` in `Elaborator.lean`). Unrecognized angles fall through to `sorry` with a warning — structural proofs (gate count, depth) are unaffected because they pattern-match on gate constructors, not angle values.

**Serializer (`Serializer.lean`) — new in v2:**
```lean
def serializeCircuit (prog : QASMProgram) (defName : String) : String
```
Emits a `noncomputable def importedCircuit : QCircuit n` by serializing the elaborated gate list with exact `Real.pi` angle expressions. Uses `<|` syntax for cons chains to avoid associativity ambiguity.

Elaboration steps:
1. Compute `n` = sum of all register sizes
2. Build register map: name → (start offset, size)
3. Resolve each `QubitRef` to `Fin n`; skip out-of-bounds with a warning
4. Fold gate list into `QCircuit n`

### CLI binary (`LeanQVerify/Main.lean`)

```bash
lean-qverify-check <file.qasm>
```

Outputs JSON:
```json
{"nQubits":2,"nGates":2,"warnings":[]}
```

Exit codes: 0 = parsed successfully, 1 = elaboration warnings, 2 = file error.

### Python bridge (`lean_qverify/`)

| Module | Purpose |
|---|---|
| `bridge.py` | `verify_circuit(qc)` — Qiskit → JSON; `verify_circuit_spec(qc, spec)` — full end-to-end structural verification → `Verdict.STRUCT_PROVED` |
| `prover.py` | `verify_structural_spec(qasm, spec)` — calls `--emit-lean`, generates theorem, runs `lake env lean`, returns `(bool, log)` |
| `result.py` | `VerifyResult` with `Verdict.{PROVED, STRUCT_PROVED, PARSED, FAILED, WARNING, ERROR}`; `kernel_checked` property |
| `gpu.py` | GPU detection via `nvidia-smi` + smoke test |
| `simulator.py` | Returns `AerSimulator` (GPU if n ≥ 20, else CPU) |
| `counterexample.py` | Batched counterexample search (CuPy or NumPy) |
| `runner.py` | Subprocess invocation of `lean-qverify-check` |

**`StructuralSpec` dataclass:**
```python
class StructSpecKind(Enum):
    GATE_COUNT = "gate_count"   # countGates (fun _ => true) c = k
    CNOT_COUNT = "cnot_count"   # countGates (.CNOT ..) c = k
    RZ_COUNT   = "rz_count"     # countGates (.RZ ..) c = k
    MAX_DEPTH  = "max_depth"    # depth c ≤ k

@dataclass
class StructuralSpec:
    kind:  StructSpecKind
    bound: int
```

**Proof strategy for structural specs:**
- Gate/CNOT/RZ count: `simp [CircuitSpec.countGates, importedCircuit]` (beta reduction via `simp` resolves `(fun _ => true) (.H ..)` → `true`)
- Depth: `simp [scheduleDepth, gateQubits, importedCircuit]` + `intro b; fin_cases b <;> simp`

---

## 8. Component 5: ZX-Calculus

**Location:** `LeanQVerify/ZX/`

### Diagram and semantics (`Diagram.lean`, `Semantics.lean`)

```lean
inductive ZXDiagram : ℕ → ℕ → Type where
  | wire     : ZXDiagram 1 1
  | hadamard : ZXDiagram 1 1
  | zSpider  : (m n : ℕ) → ℝ → ZXDiagram m n
  | xSpider  : (m n : ℕ) → ℝ → ZXDiagram m n
  | compose  : ZXDiagram m k → ZXDiagram k n → ZXDiagram m n
  | tensor   : ZXDiagram m₁ n₁ → ZXDiagram m₂ n₂ → ZXDiagram (m₁+m₂) (n₁+n₂)

-- Matrix semantics (denotational)
noncomputable def ZXDiagram.denote : ZXDiagram m n →
    Matrix (Fin (2^n)) (Fin (2^m)) ℂ
```

Notation: `ZX⟦d⟧` for `d.denote`; `d₁ ⊚ d₂` for sequential composition (d₁ first); `d₁ ↑⊗ d₂` for tensor.

### Circuit-to-ZX lemmas (`CircuitToZX.lean`)

| Theorem | Status |
|---|---|
| `hadN_unitary` — hadamard tower is unitary | ✓ |
| `zSpiderMat_11_pi` — Z(π) = Z gate | ✓ |
| `zSpiderMat_11_half_pi` — Z(π/2) = S gate | ✓ |
| `zSpiderMat_11_quarter_pi` — Z(π/4) = T gate | ✓ |
| `zGate_as_zSpider`, `sGate_as_zSpider`, `tGate_as_zSpider` | ✓ |
| `xSpider_pi_eq_X` — X(π) = X gate | ✓ |
| `xSpider_fusion` — Z-spider fusion: Z(α) ⊚ Z(β) = Z(α+β) | ✓ |
| `cnotZX_correct` — ZX representation of CNOT (up to √2 normalisation) | ✓ |
| `pi_copy` — π-copy rule: Z(π) ⊚ X-copy = X-copy ⊚ (Z(π) ↑⊗ Z(π)) | ✓ |

### Gate and circuit translation (`GateTranslation.lean`)

```lean
-- Which 1-qubit gates have direct ZX representations
def isStdGate₁ : Gate 1 → Prop
  | .H _ | .X _ | .Z _ | .S _ | .T _ => True
  | _ => False

-- Translate a standard gate to its ZX diagram
noncomputable def gateToZX₁ : Gate 1 → ZXDiagram 1 1

-- Soundness: ZX semantics = gate matrix
theorem gateToZX₁_sound (g : Gate 1) (hg : isStdGate₁ g) :
    ZX⟦gateToZX₁ g⟧ = g.matrix

-- Translate a 1-qubit circuit to a ZX diagram
noncomputable def circuitToZX₁ : QCircuit 1 → ZXDiagram 1 1

-- Circuit soundness
theorem circuitToZX₁_sound (c : QCircuit 1) (hc : isStdCircuit₁ c) :
    ZX⟦circuitToZX₁ c⟧ = c.denote
```

The translation maps H → `hadamard`, X → `xSpider 1 1 π`, Z/S/T → `zSpider 1 1 {π, π/2, π/4}`.

---

## 9. Implementation status

### Phase 1 — complete ✓

- [x] `QState n` and standard basis states
- [x] `Gate n` inductive type and all gate matrices
- [x] `QCircuit n`, `denote`, `append`, `equiv`
- [x] `embedGate1`, `embedCNOT` and composition lemmas
- [x] All gate identities (H, X, Y, Z, CNOT, conjugations, RZ, SWAP) — 10 theorems
- [x] `CircuitSpec n` and `satisfies` relation
- [x] `countGates`, `depth` (list-scheduling), `measProb`
- [x] Standard specs: Bell (5+4 joint), GHZ (2), teleportation (1), HEA (6), Grover (1) — 19 theorems
- [x] `jointMeasProb` constructor in CircuitSpec; 4 Bell joint measurement theorems
- [x] Satisfaction lemmas (monotonicity, conjunction, equivalence)
- [x] OpenQASM 3 parser and elaborator (+ OPENQASM 2.0 support)
- [x] `lean-qverify-check` CLI binary (JSON output, `--emit-lean` mode)
- [x] Python bridge (`verify_circuit`, `verify_circuit_spec`, `prover.py`, GPU detection)
- [x] Lean test suite (`TestParser`, `TestElaborator`, `TestCircuit`, `TestQState`)
- [x] `theorems/Axioms.lean` — `#print axioms` for all 29 theorems; all clean
- [x] 32-circuit benchmark suite (`benchmarks/`) with automated harness

**Total (Phase 1): 29 kernel-checked theorems. No sorry stubs in any proof tree.**

### Phase 2 — complete ✓

- [x] `DensityMatrix.ofPure` proofs (Hermiticity, PSD, unit trace) — inline in `where` clause
- [x] `DensityMatrix.applyUnitary` proofs (Hermiticity, PSD, unit trace) — inline in `where` clause
- [x] Parametric circuit families: `QFamily`, `ghzCircuit n`, `bvCircuit n` with inductive gate-count proofs
- [x] Formal QASM parser well-formedness: `wellFormed` predicate, `checkWellFormed` Bool checker, soundness theorem, concrete programs
- [ ] Formally verify Float→ℝ bridge in elaborator (out of scope for v2)
- [ ] Full teleportation correctness (requires classical communication modelling, out of scope for v2)

**Total (Phase 2): 38 kernel-checked theorems. No `sorryAx` in any proof chain.**

### Phase 3 — complete ✓

**ZX-calculus circuit translation (`GateTranslation.lean`):**

- [x] `embedGate1_one_qubit` — for n=1, embedding a 2×2 gate at qubit 0 equals the gate itself
- [x] `gateToZX₁` — certified translation of H, X, Z, S, T gates to ZX diagrams
- [x] `gateToZX₁_sound` — `ZX⟦gateToZX₁ g⟧ = g.matrix` for all supported gates
- [x] `circuitToZX₁` — certified translation of standard 1-qubit circuits to ZX diagrams
- [x] `circuitToZX₁_sound` — `ZX⟦circuitToZX₁ c⟧ = c.denote` for all standard circuits

**Total (Phase 3): 40 kernel-checked theorems. No `sorryAx` in any proof chain.**

### Future work

- [ ] `verify_circuit` tactic calling the Python bridge from within Lean
- [ ] Benchmark 20–50 qubit circuits with GPU backend
- [ ] PennyLane bridge
- [ ] Reservoir (Lean package index) submission

---

## 10. Dependencies

### Lean side

| Dependency | Version | Purpose |
|---|---|---|
| Lean 4 | 4.14.0 | Language and proof kernel |
| Mathlib4 | 4.14.0 | Complex numbers, matrices, `norm_num`, `ring` |

### Python side

| Dependency | Required | Purpose |
|---|---|---|
| qiskit ≥ 1.0 | Yes | Circuit construction and QASM export |
| qiskit-aer | Yes | CPU statevector simulation |
| qiskit-aer-gpu | Optional | GPU simulation (Linux + NVIDIA only) |
| cupy-cuda12x | Optional | GPU counterexample search |

---

## 11. GPU strategy

The Lean proof kernel is CPU-only and must remain so. GPU acceleration is confined to the Python tooling layer (Lane A):

| Component | GPU benefit | CPU fallback |
|---|---|---|
| Circuit simulation | 10–50× faster for n ≥ 20 qubits | `qiskit-aer` CPU statevector |
| Counterexample search | Batched matrix-vector ops (CuPy) | NumPy batched ops |

The threshold of 20 qubits is where GPU simulation becomes meaningfully faster than CPU. Below that, PCIe transfer overhead outweighs the compute benefit.

Runtime detection: `gpu.py` runs `nvidia-smi` once at import, then smoke-tests `AerSimulator(device='GPU')`. If either fails, `GPU_AVAILABLE = False` and all code paths use CPU silently.

GPU memory limits:

| Qubits | Statevector size | Fits in |
|---|---|---|
| 20 | 16 MB | Any GPU |
| 25 | 512 MB | Any GPU |
| 30 | 16 GB | A100 40 GB, RTX 3090 |
| 33 | 128 GB | Multi-GPU H100 |
| 35+ | > 512 GB | Not feasible on a single GPU |

---

## 12. Testing strategy

### Lean tests (at build time)

All `#guard` assertions and `example` proof obligations run during `lake build LeanQVerifyTests`. A build error means a test failed.

| File | Coverage |
|---|---|
| `TestParser.lean` | Register decls, all gate types, rotation angles, warnings, multi-register circuits |
| `TestElaborator.lean` | Gate counts, qubit counts, warning strings |
| `TestCircuit.lean` | Size, append, `denote_empty`, gate count specs, depth specs, conjunction |
| `TestQState.lean` | Normalisation proofs for all named basis states |

### Python tests

`pytest tests/python/` covers:
- `verify_circuit` happy path and warning path
- GPU detection graceful fallback
- Counterexample construction on intentionally wrong circuits

GPU-specific tests are marked `@pytest.mark.gpu` and skipped when `GPU_AVAILABLE = False`.

### Cross-validation

For every circuit in `tests/circuits/`, the JSON output of `lean-qverify-check` is compared against Qiskit Aer's statevector simulation of the same circuit. Gate count and qubit count must match.

---

*v1 scope. v2 targets: PennyLane support, noise model specs, hardware transpilation correctness, `verify_circuit` Lean tactic.*
