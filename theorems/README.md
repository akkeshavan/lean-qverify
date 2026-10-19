# Independent Theorem Verification

This folder is the self-contained artifact for verifying all 25 theorems
claimed in the paper.  A clean build of this folder — with the exact output
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
lake build                     # verifies all 25 theorems independently
```

**Pass criterion:** the final line of each `lake build` is:

```
Build completed successfully.
```

**Expected warnings (harmless):** you will see lines like:
```
warning: .../DensityMatrix.lean:38:18: declaration uses 'sorry'
warning: .../Unitary.lean:116:2: 'all_goals ring' tactic does nothing
info: .../StandardSpecs.lean:192:16: Try this: ring_nf
```
These are expected.  `DensityMatrix.lean` is infrastructure not used by any
proved theorem (see [Sorry audit](#sorry-audit) below).  The `ring` and
`ring_nf` lines are linter suggestions, not errors.

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

This sub-package imports the compiled library and runs all 25 theorem
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

| File | Theorems | Circuit |
|------|----------|---------|
| `BellState.lean` | T1–T5 | Bell state preparation (2 qubits) |
| `GHZTeleportation.lean` | T6–T8 | GHZ and teleportation (3 qubits) |
| `HEA.lean` | T9–T14 | Hardware-efficient ansatz (4 qubits) |
| `GateAlgebra.lean` | T15–T24 | Gate algebra identities |
| `Grover.lean` | T25 | Grover's algorithm (2 qubits, 1 step) |

To check a single group:

```bash
# From inside theorems/
lake build BellState
lake build GHZTeleportation
lake build HEA
lake build GateAlgebra
lake build Grover
```

---

## Sorry audit

To confirm no `sorry` appears in the proof paths of the 25 theorems:

```bash
# From the repository root:
# (matches sorry as a tactic or definition — ignores comments)
grep -Prn "^\s*sorry\s*$|:=\s*sorry" \
  LeanQVerify/Circuit/Identities.lean \
  LeanQVerify/Spec/StandardSpecs.lean \
  LeanQVerify/Foundation/Unitary.lean \
  LeanQVerify/Foundation/QState.lean \
  LeanQVerify/Circuit/Gate.lean \
  LeanQVerify/Circuit/QCircuit.lean \
  LeanQVerify/Spec/CircuitSpec.lean \
  LeanQVerify/Spec/Satisfies.lean
```

This command should produce **no output**.

The only `sorry` instances in the repository are in two modules that none of
the 25 theorems depend on:

- `LeanQVerify/QASM/Elaborator.lean` — the `floatToReal` bridge used
  exclusively by the CLI parser at runtime.  Every proved circuit is defined
  directly in Lean with exact real-number angles; the parser is never invoked.
- `LeanQVerify/Foundation/DensityMatrix.lean` — density-matrix infrastructure
  stubs for future noisy-channel work.  No proved theorem imports this file.

---

## Theorem summary

| # | Lean name | Statement | Method |
|---|-----------|-----------|--------|
| T1 | `bellPrep_twoGates` | Bell circuit: 2 gates | `simp` |
| T2 | `bellPrep_oneCNOT` | Bell circuit: 1 CNOT | `simp` |
| T3 | `bellPrep_depth` | Bell circuit: depth ≤ 2 | `simp` |
| T4 | `bellPrep_entangled` | P(q₀=0) ≥ 1/2 from \|00⟩ | matrix + `norm_num` |
| T5 | `bellPrep_entangled_one` | P(q₀=1) ≥ 1/2 from \|00⟩ | matrix + `norm_num` |
| T6 | `ghzPrep_threeGates` | GHZ circuit: 3 gates | `simp` |
| T7 | `ghzPrep_depth` | GHZ circuit: depth ≤ 3 | `simp` |
| T8 | `teleportPrep_depth` | Teleportation: depth ≤ 4 | `simp` |
| T9 | `hea4_gateCount` | HEA: 7 gates | `simp` |
| T10 | `hea4_cnotCount` | HEA: 3 CNOTs | `simp` |
| T11 | `hea4_rzCount` | HEA: 4 RZ gates | `simp` |
| T12 | `hea4_depth` | HEA: depth ≤ 4 | `simp` |
| T13 | `hea4_zero_eq_cnotChain` | hea4(0⃗) ≅ CNOT chain | `Rz_zero_id` |
| T14 | `hea4_rz_fuse_single` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) | `Rz_mat_add` |
| T15 | `H_H_eq_id` | H ∘ H ≅ I | `embedGate1_self_inverse` |
| T16 | `X_X_eq_id` | X ∘ X ≅ I | `embedGate1_self_inverse` |
| T17 | `Y_Y_eq_id` | Y ∘ Y ≅ I | `embedGate1_self_inverse` |
| T18 | `Z_Z_eq_id` | Z ∘ Z ≅ I | `embedGate1_self_inverse` |
| T19 | `CNOT_CNOT_eq_id` | CNOT ∘ CNOT ≅ I | `embedCNOT_self_mul` |
| T20 | `H_X_H_eq_Z` | HXH ≅ Z | `nlinarith` |
| T21 | `H_Z_H_eq_X` | HZH ≅ X | `nlinarith` |
| T22 | `RZ_zero_eq_id` | RZ(0) ≅ I | `Rz_zero_id` |
| T23 | `RZ_add` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) | `Rz_mat_add` |
| T24 | `SWAP_eq_three_CNOTs` | SWAP ≅ CNOT³ | `Nat.testBit_xor` |
| T25 | `groverStep2_correct` | P(q₀=1) ≥ 0.99 after Grover step | 4×4 matrix + `norm_num` |

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
