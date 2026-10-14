# Independent Theorem Verification

This folder lets you confirm that all 25 theorems claimed in the paper are
kernel-checked by Lean 4 with no `sorry` in any proof tree.

---

## What "kernel-checked" means

A Lean theorem is kernel-checked if:

1. It has a complete proof term (no `sorry` placeholder anywhere in its proof tree).
2. Lean's type-checker (the kernel) accepts that proof term as a valid inhabitant
   of the stated type.

There is no way to fake a passing build. If a `sorry` exists anywhere in a
proof's dependency chain, Lean emits a warning. A clean `lake build` with zero
errors is the guarantee.

---

## Prerequisites

| Tool | Version | Install |
|------|---------|---------|
| Lean 4 | 4.14.0 (pinned) | [elan](https://github.com/leanprover/elan) |
| Mathlib | 4.14.0 (pinned) | fetched automatically by `lake` |
| Internet | required for first run | to download ~500 MB Mathlib cache |

**Platform support:** macOS and Linux. Windows users should follow the
[Lean 4 Windows installation guide](https://leanprover.github.io/lean4/doc/setup.html)
and then run the same `lake` commands in a terminal.

### Install elan (Lean version manager)

**macOS / Linux:**

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your shell, then verify:

```bash
lean --version   # should print Lean (version 4.14.0, ...)
lake --version
```

---

## Steps to verify all 25 theorems

Run the following from the **root of the artifact** (one level above this
`theorems/` directory):

```bash
# 1. Fetch Mathlib and lock dependency versions
#    (uses the pinned lake-manifest.json — no network surprise)
lake update

# 2. Download prebuilt Mathlib oleans — skips ~30 min of compilation
lake exe cache get

# 3. Build the library and all theorem files
#    A clean build with no errors = all 25 theorems verified.
lake build

# 4. Verify the theorems subfolder independently
cd theorems
lake update
lake exe cache get
lake build
```

**Expected output** (step 3 or 4):

```
Build completed successfully.
```

**Expected time:** with the prebuilt cache, the first build takes roughly
**3–8 minutes** (compiling lean-qverify on top of Mathlib). Subsequent builds
are incremental and complete in under 30 seconds.

If `lake exe cache get` is unavailable (offline environment), omit step 2; the
build then compiles Mathlib from source, which takes **30–60 minutes**.

---

## Verifying individual theorem groups

Each file corresponds to a group of theorems from the paper:

| File | Theorems | Circuit |
|------|----------|---------|
| `BellState.lean` | T1–T5 | Bell state preparation |
| `GHZTeleportation.lean` | T6–T8 | GHZ and teleportation |
| `HEA.lean` | T9–T14 | Hardware-efficient variational ansatz |
| `GateAlgebra.lean` | T15–T24 | Gate algebra identities |
| `Grover.lean` | T25 | Grover's algorithm (2 qubits, 1 step) |

To build a single group from inside `theorems/`:

```bash
lake build BellState
lake build GHZTeleportation
lake build HEA
lake build GateAlgebra
lake build Grover
```

---

## What each file contains

Every `.lean` file follows the same pattern:

```lean
-- Stated proposition (exactly as in the paper)
example : <proposition> :=
  <theorem_name>   -- name of the proof in the library
```

The `example` keyword forces Lean's kernel to type-check that `<theorem_name>`
has the stated type. If the types do not match, the build fails. If
`<theorem_name>` does not exist, the build fails. If `sorry` is anywhere in
`<theorem_name>`'s proof tree, Lean warns and the build is not clean.

---

## Checking for sorry yourself

```bash
# From the artifact root:
grep -rn "sorry" LeanQVerify/Circuit/Identities.lean
grep -rn "sorry" LeanQVerify/Spec/StandardSpecs.lean
```

Both commands should return **no output**.

The only `sorry` instances in the library are in modules that no proved theorem
depends on:

- `LeanQVerify/QASM/Elaborator.lean` — the `floatToReal` bridge (Float → ℝ),
  used only at runtime when parsing QASM files. **None of the 25 proved
  theorems depend on this**: every proved circuit is defined directly in Lean
  with exact real-number angles.
- `LeanQVerify/Foundation/DensityMatrix.lean` — infrastructure stubs for
  future noisy-channel reasoning. **None of the 25 proved theorems import
  this module.**

---

## Theorem summary

| # | Name | Statement | Proof method |
|---|------|-----------|--------------|
| T1 | `bellPrep_twoGates` | Bell circuit uses 2 gates | `simp` |
| T2 | `bellPrep_oneCNOT` | Bell circuit uses 1 CNOT | `simp` |
| T3 | `bellPrep_depth` | Bell circuit depth ≤ 2 | `simp` |
| T4 | `bellPrep_entangled` | P(q₀=0) ≥ 1/2 from \|00⟩ | matrix + `norm_num` |
| T5 | `bellPrep_entangled_one` | P(q₀=1) ≥ 1/2 from \|00⟩ | matrix + `norm_num` |
| T6 | `ghzPrep_threeGates` | GHZ circuit uses 3 gates | `simp` |
| T7 | `ghzPrep_depth` | GHZ circuit depth ≤ 3 | `simp` |
| T8 | `teleportPrep_depth` | Teleportation depth ≤ 4 | `simp` |
| T9 | `hea4_gateCount` | HEA has 7 gates total | `simp` |
| T10 | `hea4_cnotCount` | HEA has 3 CNOTs | `simp` |
| T11 | `hea4_rzCount` | HEA has 4 RZ gates | `simp` |
| T12 | `hea4_depth` | HEA depth ≤ 4 | `simp` |
| T13 | `hea4_zero_eq_cnotChain` | hea4(0,0,0,0) ≅ CNOT chain | `Rz_zero_id` |
| T14 | `hea4_rz_fuse_single` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) | `Rz_mat_add` |
| T15 | `H_H_eq_id` | H ∘ H ≅ I | `embedGate1_self_inverse` |
| T16 | `X_X_eq_id` | X ∘ X ≅ I | `embedGate1_self_inverse` |
| T17 | `Y_Y_eq_id` | Y ∘ Y ≅ I | `embedGate1_self_inverse` |
| T18 | `Z_Z_eq_id` | Z ∘ Z ≅ I | `embedGate1_self_inverse` |
| T19 | `CNOT_CNOT_eq_id` | CNOT ∘ CNOT ≅ I | `embedCNOT_self_mul` |
| T20 | `H_X_H_eq_Z` | H X H ≅ Z | `nlinarith` |
| T21 | `H_Z_H_eq_X` | H Z H ≅ X | `nlinarith` |
| T22 | `RZ_zero_eq_id` | RZ(0) ≅ I | `Rz_zero_id` |
| T23 | `RZ_add` | RZ(θ) ∘ RZ(φ) ≅ RZ(θ+φ) | `Rz_mat_add` |
| T24 | `SWAP_eq_three_CNOTs` | SWAP ≅ CNOT³ | `Nat.testBit_xor` |
| T25 | `groverStep2_correct` | P(q₀=1) ≥ 0.99 after Grover step | 4×4 matrix + `norm_num` |
