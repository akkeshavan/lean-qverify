# Future Work

This file tracks proof stubs and planned extensions for lean-qverify.

---

## Open Proof Stubs

### 1. `SWAP_eq_three_CNOTs` — `LeanQVerify/Circuit/Identities.lean`

**Statement:**
```lean
theorem SWAP_eq_three_CNOTs (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    ofGate (.SWAP i j) ≅
    (ofGate (.CNOT i j) ++ ofGate (.CNOT j i) ++ ofGate (.CNOT i j))
```

**Why it is hard:** After `simp [embedSWAP, embedCNOT]`, the goal reduces to
showing that for each matrix entry (a, b):

    embedSWAP n i j a b = (embedCNOT * embedCNOT * embedCNOT) a b

The CNOT product exchanges bits i and j via XOR. The key sub-goal is:

    setBit (setBit (setBit a.val i bⱼ) j bᵢ) i bⱼ' = swapped entry

where the three-CNOT composition performs XOR-based bit exchange. The
required Mathlib lemmas are `Nat.testBit_xor`, `Nat.xor_assoc`, and
`Nat.testBit_setBit_same`.

**Strategy:**
1. Show `embedCNOT n i j * embedCNOT n j i * embedCNOT n i j = embedSWAP n i j`
   entry-by-entry using `Nat.testBit_xor`.
2. The three-CNOT product maps `(aᵢ, aⱼ)` to `(aᵢ XOR (aⱼ XOR aᵢ), aⱼ XOR aᵢ)`
   then `(aᵢ XOR aⱼ XOR aᵢ XOR aⱼ XOR aᵢ, ...)` = `(aⱼ, aᵢ)` by XOR cancellation.
3. Close with `Nat.xor_assoc` and `Nat.xor_self`.

**Impact:** Not used by any proved theorem in the current codebase. Does not
block any case study.

---

### 2. `groverStep2_correct` — `LeanQVerify/Spec/StandardSpecs.lean`

**Statement:**
```lean
theorem groverStep2_correct :
    (QCircuit.ofGate (.H 0) ++ QCircuit.ofGate (.H 1) ++ groverStep2)
    ⊨ .measurementProb QState.ket00 0 true 0.99
```

**Numerical confirmation:** Qiskit Aer statevector simulation gives
P(qubit 0 = 1) = 1.0000 and P(qubit 1 = 1) = 1.0000. The spec bound
(≥ 0.99) is far below the true value.

**Why it is hard:** `groverStep2` is a 10-gate circuit (1 oracle CZ + 9
diffusion gates). Unfolding its full 4×4 unitary requires chaining
`denote_append` ten times and evaluating the resulting 4×4 matrix product
symbolically. Each `embedGate1` and `embedCNOT` call expands to a
16-entry case split. The computation is finite and mechanical but large.

**Strategy:**
1. Define `groverUnitary : Matrix (Fin 4) (Fin 4) ℂ` as the explicit
   numerical 4×4 matrix (the all-ones column in position 3).
2. Prove `groverStep2_full.denote = groverUnitary` by `norm_num` after
   fully unfolding via `denote_append`, `simp [embedGate1, embedCZ]`,
   `Fin.sum_univ_four`, and `Nat.testBit`.
3. Derive `groverStep2_correct` from step 2 by Born-rule computation
   (analogous to `bellPrep_entangled`).

**Impact:** The correctness of the Grover case study is numerically verified
but not kernel-checked. A proof would make all five case studies fully sorry-free.

---

## Phase 2: Verified Parser

Replace the trusted recursive-descent parser (`LeanQVerify/QASM/Parser.lean`)
with a `Parsec`-based parser proved correct against a formal grammar. This
closes the largest gap in the trusted computing base. The parser correctness
statement would be:

```lean
theorem parse_correct (s : String) (prog : QASMProgram) :
    parse s = .ok prog → interprets s prog
```

where `interprets` relates the string to its intended abstract syntax.

---

## Phase 3: Verified Gate Matrix Specification

Prove that each entry of `Gate.matrix` matches the standard physics definition.
For example:

```lean
theorem H_mat_correct :
    H_mat = (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]
```

This removes `Gate.matrix` from the trusted computing base.

---

## Phase 4: Extended Specification Language

- **Post-measurement specs:** A `postMeasure` constructor to handle
  teleportation correctness and error correction syndromes.
- **`forAll` constructor:** `c ⊨ .forAll_inputs (fun ψ => ...)` to express
  all-input properties as first-class `CircuitSpec` values, enabling
  composition with `both`.
- **Parametric circuit families:** `QFamily : ℕ → QCircuit n` for families
  like GHZ(n) or QFT(n), bringing lean-qverify closer to QBricks expressiveness.

---

## Phase 5: Noise Modeling

Extend `QCircuit n` with a noise channel abstraction and import
`Lean-QuantumInfo`'s channel theorems to verify error-corrected circuits
under depolarizing or amplitude-damping noise models.
