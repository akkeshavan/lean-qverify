# Verified Quantum Circuits: A Lean 4 Workbook

A hands-on guide to formally verifying quantum circuits using the lean-qverify library.

## Chapters

| # | File | Topic |
|---|------|-------|
| 1 | `Book/Ch01/` | Why formally verify quantum circuits? |
| 2 | `Book/Ch02/` | Setup: Lean 4, elan, lake |
| 3 | `Book/Ch03/` | Quantum states in Lean |
| 4 | `Book/Ch04/` | Gates |
| 5 | `Book/Ch05/` | Circuits |
| 6 | `Book/Ch06/` | Specifications |
| 7 | `Book/Ch07/` | Structural proofs (gate count, depth) |
| 8 | `Book/Ch08/` | Semantic proofs (output probabilities) |
| 9 | `Book/Ch09/` | Parametric circuit families |
| 10 | `Book/Ch10/` | The Python bridge |
| 11 | `Book/Ch11/` | Quantum Hoare Logic |
| 12 | `Book/Ch12/` | ZX-Calculus |

Each chapter has a `prose.md` (the text) and a `.lean` file (the code).

## Build everything

From the **repository root** (the directory above `book/`), build the library first:

```bash
lake update
lake exe cache get
lake build
```

Then from this `book/` directory:

```bash
lake update
lake exe cache get   # fast: same Mathlib version, already cached
lake build
```

## Build a single chapter

```bash
# From inside book/
lake build Book.Ch03.QStates
lake build Book.Ch07.StructuralProofs
lake build Book.Ch09.ParametricFamilies
```

## How the Mathlib cache works

The `book/` project and the root project use the same Lean version and the same Mathlib version. The prebuilt `.olean` files are fetched from the same source. On most machines, `lake exe cache get` in `book/` is fast after running it in the root — the files are already downloaded.

The `book/.lake/` directory is separate from the root `.lake/`. They do not share compiled output, but they share the same download cache.
