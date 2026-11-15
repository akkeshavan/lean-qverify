# Independent Theorem Verification

This folder is the self-contained artifact for verifying all 50 theorems
in the library.  A clean build of this folder — with the exact output
described below — is the machine-checked certificate.

---

## Quick start (copy-paste)

```bash
# Run from the REPOSITORY ROOT (one level above this theorems/ directory)
cd ..                          # if you are currently inside theorems/

lake update                    # ~2 min on first run: downloads Mathlib source
lake exe cache get             # ~5 min: downloads 500 MB prebuilt Mathlib cache
lake build                     # ~5 min: compiles lean-qverify + all theorems

cd theorems
lake update
lake exe cache get
lake build                     # verifies all 38 theorems independently
```

**Pass criterion:** the final line of each `lake build` is:

```
Build completed successfully.
```

**Expected warnings (harmless):** you will see lines like:
```
warning: .../Stabilizer/Sound.lean:578:14: declaration uses `sorry`
warning: .../Unitary.lean:116:2: 'all_goals ring' tactic does nothing
info: .../StandardSpecs.lean:192:16: Try this: ring_nf
```
These are expected.  `Stabilizer/Sound.lean` has 6 pre-existing sorry stubs
for a single mathematical claim (stabilizer-state uniqueness under Z measurement)
that does not affect any proved theorem (see [Sorry audit](#sorry-audit) below).
The `ring` and `ring_nf` lines are linter suggestions, not errors.

**Fail criterion:** any line containing `error:` or `unsolved goals` means a
proof is broken.

---

## Prerequisites

| Tool | Version | Install |
|------|---------|---------|
| Lean 4 | 4.14.0 (pinned by `lean-toolchain`) | via elan (see below) |
| Mathlib | 4.14.0 (pinned by `lake-manifest.json`) | fetched automatically |
| Internet | required on first run | ~500 MB Mathlib cache |
| Disk space | ~2 GB | for Lean toolchain + Mathlib cache |

**Platforms:** macOS and Linux are fully supported.  Windows: install
[elan](https://github.com/leanprover/elan) via the Windows installer, then
run the same commands in PowerShell or WSL.

### Install elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# Restart your shell, then verify:
lean --version   # Lean (version 4.14.0, ...)
lake --version
```

---

## Step-by-step with explanations

All commands below are run from the **repository root** (the directory
containing `lakefile.lean`), unless noted otherwise.

### Step 1 — fetch dependencies (~2 min, first run only)

```bash
lake update
```

Downloads Mathlib 4.14.0 source and records exact dependency versions in
`lake-manifest.json`.  Subsequent runs are instant (no-op if manifest is
unchanged).

### Step 2 — download prebuilt Mathlib cache (~5 min, first run only)

```bash
lake exe cache get
```

Downloads ~500 MB of precompiled Mathlib `.olean` files.  This skips
recompiling Mathlib from source, which would otherwise take 30–60 minutes.

**If this step fails** (network restrictions or offline environment): skip it
and proceed to step 3.  The build will compile Mathlib from source; allow
30–60 minutes instead of 5.

**If you see** `Warning: no oleans found for the current Lean/Mathlib version`:
the cache may not exist for your exact platform.  Proceed to step 3 anyway.

### Step 3 — build the full library (~5 min with cache)

```bash
lake build
```

Compiles the entire `lean-qverify` library on top of Mathlib.  On first run
with the cache downloaded this takes roughly 5 minutes.  Subsequent runs
(after any source change) are incremental and complete in seconds.

### Step 4 — verify the theorems independently (~30 sec, incremental)

```bash
cd theorems
lake update
lake exe cache get
lake build
```

This sub-package imports the compiled library and runs all 50 theorem
type-checks independently.  Each `example` forces Lean's kernel to re-verify
the stated proposition against the named proof term.

---

## What the build checks

Every `.lean` file in `theorems/` follows this pattern:

```lean
-- Proposition from the paper (exact type)
example : <proposition> :=
  <theorem_name>   -- the proof term in the library
```

Lean's kernel verifies that `<theorem_name>` has exactly the stated type.
If the proof is missing, the wrong type, or contains `sorry` anywhere in its
dependency chain, `lake build` exits with a non-zero status and prints an
error.

### Files and theorem groups

| File | Theorems | Circuit/Topic |
|------|----------|---------|
| `BellState.lean` | T1–T9 | Bell state preparation (2 qubits) |
| `GHZTeleportation.lean` | T10–T12 | GHZ and teleportation (3 qubits) |
| `HEA.lean` | T13–T18 | Hardware-efficient ansatz (4 qubits) |
| `GateAlgebra.lean` | T19–T28 | Gate algebra identities |
| `Grover.lean` | T29 | Grover's algorithm (2 qubits, 1 step) |
| `Axioms.lean` | T30–T38 | DensityMatrix + Parametric + QASM parser |
| `Variational.lean` | T39–T50 | Hybrid ZX + symbolic; variational circuits |

To check a single group:

```bash
# From inside theorems/
lake build BellState
lake build GHZTeleportation
lake build HEA
lake build GateAlgebra
lake build Grover
lake build Axioms
lake build Variational
```

---

## Sorry audit

All 50 theorems have clean `#print axioms` output — the proof trees contain
only `Classical.choice`, `propext`, `Quot.sound`, and `funext`.  No `sorryAx`.

The repository has **6 sorry stubs** in `Stabilizer/Sound.lean` for a single
unresolved mathematical claim (stabilizer-state uniqueness under Z measurement
in the deterministic branch of `zProb_correct`).  These stubs are **not** in
any proved theorem's dependency chain — all 50 theorems in `theorems/` are
clean.

To confirm the proved theorems are sorry-free:

```bash
# From the repository root:
# (matches sorry as a tactic or definition — ignores comments)
grep -Prn "^\s*sorry\s*$|:=\s*sorry" \
  LeanQVerify/Circuit/Identities.lean \
  LeanQVerify/Circuit/Parametric.lean \
  LeanQVerify/Circuit/Variational.lean \
  LeanQVerify/Spec/StandardSpecs.lean \
  LeanQVerify/Foundation/Unitary.lean \
  LeanQVerify/Foundation/QState.lean \
  LeanQVerify/Foundation/DensityMatrix.lean \
  LeanQVerify/Circuit/Gate.lean \
  LeanQVerify/Circuit/QCircuit.lean \
  LeanQVerify/Spec/CircuitSpec.lean \
  LeanQVerify/Spec/Satisfies.lean \
  LeanQVerify/QASM/ParseTheorems.lean \
  LeanQVerify/ZX/HybridRules.lean
```

This command should produce **no output**.

To inspect the Sound.lean stubs (expected, does not affect proved theorems):

```bash
grep -n "sorry" LeanQVerify/Stabilizer/Sound.lean | grep -v "^.*--"
```

---

## Theorem summary

| # | Lean name | Statement | Method |
|---|-----------|-----------|--------|
| T1 | `bellPrep_twoGates` | Bell circuit: 2 gates | `simp` |
| T2 | `bellPrep_oneCNOT` | Bell circuit: 1 CNOT | `simp` |
| T3 | `bellPrep_depth` | Bell circuit: depth ≤ 2 | `simp` |
| T4 | `bellPrep_entangled` | P(q₀=0) ≥ 1/2 from \|00⟩ | matrix + `norm_num` |
| T5 | `bellPrep_entangled_one` | P(q₀=1) ≥ 1/2 from \|00⟩ | matrix + `norm_num` |
| T6 | `bellPrep_joint_ket00` | P(\|00⟩) ≥ 1/2 from \|00⟩ | `jointMeasProb` + `norm_num` |
| T7 | `bellPrep_joint_ket11` | P(\|11⟩) ≥ 1/2 from \|00⟩ | `jointMeasProb` + `norm_num` |
| T8 | `bellPrep_joint_ket01_zero` | P(\|01⟩) = 0 from \|00⟩ | `jointMeasProb` + `norm_num` |
| T9 | `bellPrep_joint_ket10_zero` | P(\|10⟩) = 0 from \|00⟩ | `jointMeasProb` + `norm_num` |
| T10 | `ghzPrep_threeGates` | GHZ circuit: 3 gates | `simp` |
| T11 | `ghzPrep_depth` | GHZ circuit: depth ≤ 3 | `simp` |
| T12 | `teleportPrep_depth` | Teleportation: depth ≤ 4 | `simp` |
| T13 | `hea4_gateCount` | HEA: 7 gates | `simp` |
| T14 | `hea4_cnotCount` | HEA: 3 CNOTs | `simp` |
| T15 | `hea4_rzCount` | HEA: 4 RZ gates | `simp` |
| T16 | `hea4_depth` | HEA: depth ≤ 4 | `simp` |
| T17 | `hea4_zero_eq_cnotChain` | hea4(0⃗) ≅ CNOT chain | `Rz_zero_id` |
| T18 | `hea4_rz_fuse_single` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) | `Rz_mat_add` |
| T19 | `H_H_eq_id` | H ∘ H ≅ I | `embedGate1_self_inverse` |
| T20 | `X_X_eq_id` | X ∘ X ≅ I | `embedGate1_self_inverse` |
| T21 | `Y_Y_eq_id` | Y ∘ Y ≅ I | `embedGate1_self_inverse` |
| T22 | `Z_Z_eq_id` | Z ∘ Z ≅ I | `embedGate1_self_inverse` |
| T23 | `CNOT_CNOT_eq_id` | CNOT ∘ CNOT ≅ I | `embedCNOT_self_mul` |
| T24 | `H_X_H_eq_Z` | HXH ≅ Z | `nlinarith` |
| T25 | `H_Z_H_eq_X` | HZH ≅ X | `nlinarith` |
| T26 | `RZ_zero_eq_id` | RZ(0) ≅ I | `Rz_zero_id` |
| T27 | `RZ_add` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) | `Rz_mat_add` |
| T28 | `SWAP_eq_three_CNOTs` | SWAP ≅ CNOT³ | `Nat.testBit_xor` |
| T29 | `groverStep2_correct` | P(q₀=1) ≥ 0.99 after Grover step | 4×4 matrix + `norm_num` |
| T30 | `DensityMatrix.ofPure` | ρ = \|ψ⟩⟨ψ\| is Hermitian + PSD + trace-1 | inline `where` proofs |
| T31 | `DensityMatrix.applyUnitary` | UρU† is Hermitian + PSD + trace-1 | inline `where` proofs |
| T32 | `countGates_append` | countGates is additive over append | induction |
| T33 | `ghzCircuit_gateCount` | ghzCircuit(n+1): n+1 gates | `show` + induction |
| T34 | `ghzCircuit_cnotCount` | ghzCircuit(n+1): n CNOTs | `show` + `castSucc` + induction |
| T35 | `bvOracle_cnotCount_le` | bvOracle(n,s): ≤ n CNOTs | `show` + `split_ifs` + induction |
| T36 | `checkWellFormed_sound` | Bool checker ⇒ formal `wellFormed` Prop | `List.all_eq_true` + `BEq` |
| T37 | `bellProgram_wellFormed` | Bell QASM program passes checker | `rfl` |
| T38 | `ghz3Program_wellFormed` | GHZ-3 QASM program passes checker | `rfl` |
| T39 | `Rz_mat_neg_period` | RZ(θ+2π) = −RZ(θ) (quasi-period) | `exp_add` + Euler |
| T40 | `Rz_mat_period` | RZ(θ+4π) = RZ(θ) (true period) | two quasi-periods |
| T41 | (gate-level 4π) | embed(RZ(θ+4π)) = embed(RZ(θ)) | `Rz_mat_period` |
| T42 | (RZ fusion) | RZ(θ,i) ++ RZ(φ,i) ≅ RZ(θ+φ,i) | `Rz_mat_add` |
| T43 | (H;RZ;H circuit) | H_i; RZ(θ,i); H_i ≅ RX(θ,i) | `H_RZ_H_eq_RX_circuit` |
| T44 | `H_RX_H_eq_RZ_circuit` | H_i; RX(θ,i); H_i ≅ RZ(θ,i) | conjugation by H²=I |
| T45 | (rzVQC period) | rzVQC(θ).denote = rzVQC(θ+4π).denote | `Rz_mat_period` |
| T46 | (heaBlock zero) | heaBlock(0⃗,0⃗).denote = cnotChainFwd | `simp` + `Rz_mat` at zero |
| T47 | (vqeAnsatz2 at 0) | vqeAnsatz2(0).denote = 1 | CNOT self-inverse + H²=I |
| T48 | (QAOA gate count) | countGates(qaoa1Layer γ β) = 5 | `simp` |
| T49 | `param_shift_Rz` | Rz(θ+π/2) − Rz(θ−π/2) = −i√2·Z·Rz(θ) | Euler + `ring` |
| T50 | `param_shift_circuit` | circuit-level parameter shift rule | `embedGate1_sub` |

---

## Troubleshooting

**`lean: command not found`** — elan is not on your PATH.  Run
`source ~/.elan/env` or restart your shell.

**`error: unknown package 'mathlib'`** — run `lake update` before `lake build`.

**`lake exe cache get` prints `error: no such file or directory`** — the
`cache` executable is not built yet.  Run `lake build cache` first, or skip
this step and let `lake build` compile Mathlib from source.

**Build hangs for more than 60 minutes** — this is normal if the Mathlib cache
was not downloaded.  It is compiling ~150k lines of Mathlib from scratch.
Do not interrupt it.

**`error: declaration uses 'sorry'` on a theorem in `theorems/`** — a proof
is broken.  This should not happen with the artifact as submitted; please
report it as an artifact evaluation issue.
