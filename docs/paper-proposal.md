# LeanQVerify — Paper Proposal

*Last updated: 2026-11-15*

---

## Target Venue

Primary target: **ITP 2027** (Interactive Theorem Proving) — the flagship venue for work combining proof assistants with mathematical formalization. The library-first approach, 52 kernel-checked theorems, and Lean 4 / Mathlib4 stack are a natural fit.

Strong alternate: **CPP 2027** (Certified Programs and Proofs, ACM SIGPLAN) — covers verified software and proof engineering; the QASM parser theorems and the Python bridge angle fit well here.

Stretch target: **POPL 2027** — worth a shot if the paper foregrounds the type-theoretic design (dependent types for qubit-indexed matrices, the `Fin 2` encoding) over the quantum-physics results.

**Format:** 20-page conference paper (ITP / CPP both use this limit). The artifact (the repo + `lake build` instructions) will be submitted for artifact evaluation.

---

## Abstract (Draft)

*Informal — for a collaborator to tighten into final form.*

Quantum computing promises exponential speedups for certain problems, but verifying that quantum circuits behave as intended is surprisingly hard. Circuits are defined over complex-valued matrices, their correctness depends on subtle linear-algebraic identities, and the emerging class of variational quantum algorithms adds continuous parameter spaces on top of that.

We present **LeanQVerify**, an open-source Lean 4 library that formally verifies properties of quantum circuits using Mathlib4 as the mathematical foundation. The library contains 52 machine-checked theorems: structural properties of Bell, GHZ, and teleportation circuits; correctness of hardware-efficient ansatz and Grover-search steps; a full suite of gate-algebra identities; density-matrix axioms; a QASM parser with formal well-formedness proofs; and — as the main new contribution — a hybrid ZX-calculus + symbolic framework for variational quantum algorithms that culminates in a machine-checked proof of the **parameter shift rule**, the algebraic identity underlying gradient-based quantum optimization.

All 52 theorems are verified against Lean's trusted kernel; none depend on `sorry`. The library is released on GitHub with full artifact-evaluation instructions and an independent verification sub-package (`theorems/`) that any reviewer can build in under ten minutes.

---

## Technical Contributions

1. **LeanQVerify library** — a reusable, open-source Lean 4 library for quantum circuit verification. Built on Mathlib4; circuits are first-class objects with `countGates`, `depth`, `denote` (matrix semantics), and `wellFormed` predicates. All public API is kernel-checked.

2. **52 machine-checked theorems** — spanning Bell states, GHZ, teleportation, hardware-efficient ansatz, Grover, gate algebra, density matrices, QASM parsing, and variational circuits. No theorem depends on `sorry`; `#print axioms` on every result shows only `Classical.choice`, `propext`, `Quot.sound`, `funext`.

3. **Hybrid ZX + symbolic framework** — a new two-layer architecture for variational quantum circuits. The Clifford skeleton is rewritten using ZX-calculus rules; rotation angles are handled by symbolic trig algebra (`Rz_mat_add`, `H_Rz_H_eq_Rx`). The split lets the two concerns be verified independently.

4. **Machine-checked parameter shift rule** — the first (to our knowledge) machine-checked proof of `Rz(θ+π/2) − Rz(θ−π/2) = −i√2 · Z·Rz(θ)` and its circuit-level corollary, the foundation of gradient computation in variational quantum algorithms.

5. **QASM parser with well-formedness theorems** — a Lean 4 parser for a subset of OpenQASM 2.0 together with proofs that standard programs (`bellProgram`, `ghz3Program`) satisfy the formal `wellFormed` predicate.

6. **Python bridge** — a Qiskit-backed simulation layer that lets users synthesize candidate circuits in Python, export to QASM, and either verify or find counterexamples, with GPU acceleration via Qiskit-Aer.

7. **Artifact** — a self-contained `theorems/` sub-package that any reviewer can build from scratch in under 10 minutes, producing an independent machine-checked certificate for all 52 theorems.

---

## Results to Publish

52 theorems in 7 groups. All kernel-checked; zero `sorry` in proved chains.

### Group 1 — Bell state preparation (T1–T9)

| # | Lean name | Statement |
|---|-----------|-----------|
| T1 | `bellPrep_twoGates` | Bell circuit uses exactly 2 gates |
| T2 | `bellPrep_oneCNOT` | Bell circuit uses exactly 1 CNOT |
| T3 | `bellPrep_depth` | Bell circuit depth ≤ 2 |
| T4 | `bellPrep_entangled` | P(q₀=0) ≥ 1/2 from \|00⟩ |
| T5 | `bellPrep_entangled_one` | P(q₀=1) ≥ 1/2 from \|00⟩ |
| T6 | `bellPrep_joint_ket00` | P(\|00⟩) ≥ 1/2 from \|00⟩ |
| T7 | `bellPrep_joint_ket11` | P(\|11⟩) ≥ 1/2 from \|00⟩ |
| T8 | `bellPrep_joint_ket01_zero` | P(\|01⟩) = 0 from \|00⟩ |
| T9 | `bellPrep_joint_ket10_zero` | P(\|10⟩) = 0 from \|00⟩ |

### Group 2 — GHZ and teleportation (T10–T12)

| # | Lean name | Statement |
|---|-----------|-----------|
| T10 | `ghzPrep_threeGates` | GHZ circuit: 3 gates |
| T11 | `ghzPrep_depth` | GHZ circuit: depth ≤ 3 |
| T12 | `teleportPrep_depth` | Teleportation circuit: depth ≤ 4 |

### Group 3 — Hardware-efficient ansatz (T13–T18)

| # | Lean name | Statement |
|---|-----------|-----------|
| T13 | `hea4_gateCount` | HEA(4-qubit): 7 gates |
| T14 | `hea4_cnotCount` | HEA(4-qubit): 3 CNOTs |
| T15 | `hea4_rzCount` | HEA(4-qubit): 4 RZ gates |
| T16 | `hea4_depth` | HEA(4-qubit): depth ≤ 4 |
| T17 | `hea4_zero_eq_cnotChain` | hea4(0⃗) reduces to CNOT chain |
| T18 | `hea4_rz_fuse_single` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) |

### Group 4 — Gate algebra (T19–T28)

| # | Lean name | Statement |
|---|-----------|-----------|
| T19–T22 | `H/X/Y/Z_..._eq_id` | H²=X²=Y²=Z²=I |
| T23 | `CNOT_CNOT_eq_id` | CNOT² = I |
| T24 | `H_X_H_eq_Z` | HXH = Z |
| T25 | `H_Z_H_eq_X` | HZH = X |
| T26 | `RZ_zero_eq_id` | RZ(0) = I |
| T27 | `RZ_add` | RZ(θ) ∘ RZ(φ) = RZ(θ+φ) |
| T28 | `SWAP_eq_three_CNOTs` | SWAP = CNOT³ |

### Group 5 — Grover's algorithm (T29)

| # | Lean name | Statement |
|---|-----------|-----------|
| T29 | `groverStep2_correct` | P(q₀=1) ≥ 0.99 after one Grover step (2-qubit) |

### Group 6 — Density matrix + QASM (T30–T38)

| # | Lean name | Statement |
|---|-----------|-----------|
| T30 | `DensityMatrix.ofPure` | \|ψ⟩⟨ψ\| is Hermitian, PSD, trace-1 |
| T31 | `DensityMatrix.applyUnitary` | UρU† is Hermitian, PSD, trace-1 |
| T32 | `countGates_append` | countGates is additive over append |
| T33 | `ghzCircuit_gateCount` | ghzCircuit(n+1) has n+1 gates |
| T34 | `ghzCircuit_cnotCount` | ghzCircuit(n+1) has n CNOTs |
| T35 | `bvOracle_cnotCount_le` | bvOracle(n,s) has ≤ n CNOTs |
| T36 | `checkWellFormed_sound` | Bool checker ⇒ formal `wellFormed` |
| T37 | `bellProgram_wellFormed` | Bell QASM program is well-formed |
| T38 | `ghz3Program_wellFormed` | GHZ-3 QASM program is well-formed |

### Group 7 — Variational circuits (T39–T50) — *main new contribution*

| # | Lean name | Statement |
|---|-----------|-----------|
| T39 | `Rz_mat_neg_period` | RZ(θ+2π) = −RZ(θ) (quasi-period) |
| T40 | `Rz_mat_period` | RZ(θ+4π) = RZ(θ) (true period) |
| T41 | — | Embedded RZ has 4π periodicity |
| T42 | — | RZ fusion at circuit level |
| T43 | `H_RZ_H_eq_RX_circuit` | Hᵢ; RZ(θ,i); Hᵢ ≅ RX(θ,i) |
| T44 | `H_RX_H_eq_RZ_circuit` | Hᵢ; RX(θ,i); Hᵢ ≅ RZ(θ,i) |
| T45 | — | rzVQC(θ) and rzVQC(θ+4π) have same denotation |
| T46 | — | heaBlock(0⃗,0⃗) reduces to CNOT chain |
| T47 | — | vqeAnsatz2(0) = identity |
| T48 | — | qaoa1Layer gate count = 5 |
| T49 | `param_shift_Rz` | RZ(θ+π/2)−RZ(θ−π/2) = −i√2·Z·RZ(θ) |
| T50 | `param_shift_circuit` | Circuit-level parameter shift rule |

---

## Related Work and Citations

### Closest prior work — formal verification of quantum circuits

| Work | System | What they prove | Key difference |
|------|--------|-----------------|----------------|
| SQIR / VOQC (Hietala et al., POPL 2021) | Coq | Correctness of Grover, QPE, Deutsch-Jozsa; verified optimizer | Coq; no variational circuits; no parameter shift |
| Coq-Q (Zhou et al., POPL 2023) | Coq | Quantum programs with classical control | Different model (programs, not gate circuits) |
| VyZX (Lehmann & Rand, CPP 2022) | Coq | ZX-calculus rewriting rules | No connection to quantum algorithms or VQA |
| Qbricks (Chareton et al., CAV 2021) | Why3 | Quantum program verification | Different prover; no Lean/Mathlib ecosystem |
| Formal QC in Isabelle (Bordg et al., 2021) | Isabelle | No-cloning, teleportation | Smaller scope; no circuit structure |

*Our differentiator:* Lean 4 + Mathlib4; variational / parametric circuits; parameter shift rule; QASM parser; Python bridge.

### ZX-calculus

- Coecke, B. & Duncan, R. (2008). *Interacting quantum observables.* ICALP. — Original ZX-calculus paper.
- van de Wetering, J. (2020). *ZX-calculus for the working quantum computer scientist.* arXiv:2012.13966. — Comprehensive reference; we cite this for the spider fusion and colour-change rules used in `HybridRules.lean`.
- Kissinger, A. & van de Wetering, J. (2019). *PyZX: Large scale automated diagrammatic reasoning.* QPL. — Python tool (not formally verified); contrast for the unverified baseline.

### Lean 4 and Mathlib

- de Moura, L. & Ullrich, S. (2021). *The Lean 4 theorem prover and programming language.* CADE-28. — Cite for the proof assistant itself.
- The Mathlib Community (2020). *The Lean mathematical library.* CPP. — Cite for Mathlib4; we depend on `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`, `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`, and `norm_num` / `ring` tactics.

### Variational quantum algorithms

- Cerezo, M. et al. (2021). *Variational quantum algorithms.* Nature Reviews Physics 3, 625–644. — Survey; cite for VQE, QAOA motivation.
- Mitarai, K. et al. (2018). *Quantum circuit learning.* Physical Review A 98, 032309. — First parameter shift rule paper.
- Schuld, M. et al. (2019). *Evaluating analytic gradients on quantum hardware.* Physical Review A 99, 032331. — Generalised parameter shift; we prove the Rz case.
- Kandala, A. et al. (2017). *Hardware-efficient variational quantum eigensolver for small molecules.* Nature 549, 242–246. — HEA architecture we formalise in T13–T18.

### Quantum algorithms

- Grover, L. K. (1996). *A fast quantum mechanical algorithm for database search.* STOC. — T29.
- Bennett, C. H. et al. (1993). *Teleporting an unknown quantum state.* PRL 70, 1895. — T12.
- Greenberger, D., Horne, M. & Zeilinger, A. (1989). *Going beyond Bell's theorem.* In *Bell's Theorem, Quantum Theory and Conceptions of the Universe.* — T10–T11.
- Bell, J. S. (1964). *On the Einstein-Podolsky-Rosen paradox.* Physics 1(3), 195–200. — Background for T1–T9.

### OpenQASM

- Cross, A. W. et al. (2017). *Open quantum assembly language.* arXiv:1707.03429. — The QASM subset we parse in T36–T38.

### Proof-assistant tooling

- Qiskit Development Team (2017–). *Qiskit: An open-source framework for quantum computing.* — Used in the Python bridge.
- Avigad, J. & Harrison, J. (2014). *Formally verified mathematics.* Comm. ACM. — Background on library-first formal verification approach.

---

## Proposed Paper Structure

20 pages for ITP / CPP. Suggested section allocation:

| § | Title | Pages | Content |
|---|-------|-------|---------|
| 1 | Introduction | 2 | Why formal QC verification is hard; what we built; paper map |
| 2 | Background | 2 | Lean 4 + Mathlib4; quantum circuit model (qubits, unitary matrices, measurement); ZX-calculus basics |
| 3 | Library Architecture | 2 | Five layers: Foundation → Circuit → Spec → ZX → QASM; key design choices (`Fin n` for qubit indices; `Matrix (Fin 2) (Fin 2) ℂ`; circuit as `List Gate`) |
| 4 | Core Circuit Theorems (T1–T29) | 4 | Bell, GHZ, teleportation, HEA, gate algebra, Grover; highlight the `jointMeasProb` framework for entanglement (T6–T9) |
| 5 | Density Matrices and QASM (T30–T38) | 2 | `DensityMatrix` structure; `checkWellFormed_sound` proof technique; QASM parser |
| 6 | Variational Circuits (T39–T50) | 4 | The hybrid ZX+symbolic framework; `H_Rz_H_eq_Rx` proof walk-through; parameter shift rule |
| 7 | Python Bridge | 1 | Architecture; Qiskit + GPU backend; counterexample workflow |
| 8 | Evaluation | 1 | Build times; sorry audit; comparison table with SQIR/Coq-Q/VyZX |
| 9 | Related Work | 1 | (abbreviated — bulk is in §2 and §8) |
| 10 | Conclusion | 1 | Summary; open problems |

**Key proof to highlight:** The `H_Rz_H_eq_Rx` proof (T43) is a good narrative centrepiece — it touches the `fin_cases` / `Fin.mk` elaboration subtlety, the `↑θ/2` vs `↑(θ/2)` coercion issue, and the `hs2 : (sqrt 2)⁻¹² = 1/2` auxiliary — concrete enough to show how Lean 4 + Mathlib handles complex-matrix algebra.

---

## Further Research Directions

Ordered roughly by feasibility and payoff for a follow-on paper.

**Short-term (closes open items in this paper)**

- **Close the 6 Sound.lean sorries.** The open claim is stabilizer-state uniqueness under Z measurement in the deterministic branch of `zProb_correct`. This is a purely mathematical lemma about density matrices that should be provable from Mathlib's linear algebra. Probably 1–2 weeks of Lean work for someone familiar with the codebase.
- **Full ZX-calculus completeness.** We use ZX rewriting rules but do not prove completeness (every true ZX equality is derivable). VyZX (Lehmann & Rand) has a Coq proof; porting or reproducing in Lean 4 would make the hybrid framework self-contained.

**Medium-term (new paper territory)**

- **Formally verified quantum compilation.** Extend LeanQVerify into a VOQC-style verified optimizer: prove that gate-cancellation, commutation, and routing passes preserve circuit semantics. The `denote` function is the natural correctness criterion.
- **Multi-qubit parameter shift rules.** We proved the single-qubit Rz case. The generalised parameter shift (Schuld et al.) applies to any gate of the form exp(−iθP/2) for a Pauli P. A Lean proof for the general case would cover VQE and QAOA analytically.
- **Quantum error correction.** Formalise the stabilizer formalism (the 6 Sound.lean sorries are the entry point), then prove basic QEC properties: the [[7,1,3]] Steane code, the [[5,1,3]] perfect code, or at least the 3-qubit repetition code.
- **PennyLane integration.** A PennyLane backend for the Python bridge would let users run the verified gradient rules against autograd and check numerical agreement, giving a formal/empirical cross-check.

**Long-term (ambitious)**

- **Quantum advantage verification.** Formally verify that a specific circuit family achieves a provable quantum speedup (e.g., Bernstein-Vazirani, Simon's algorithm) relative to a formally defined classical lower bound.
- **Noise models and approximate verification.** Extend the density matrix framework with Kraus operators for depolarising noise, then prove approximate rather than exact correctness — relevant for NISQ-era circuits.
- **Connection to Rust/C++ simulation kernels.** Use Lean 4's FFI to call a verified-correct C++ state-vector kernel, closing the gap between the Lean proof and actual hardware execution.
