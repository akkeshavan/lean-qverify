import Lake
open Lake DSL

package «lean-qverify» where
  version     := v!"0.1.0"
  description := "Formal verification of quantum circuits in Lean 4 + Mathlib: " ++
                 "type-safe gate/circuit model, ZX-calculus semantics, " ++
                 "OpenQASM 3 parser, and a circuit specification language."
  keywords    := #["quantum-computing", "formal-verification", "zx-calculus",
                   "lean4", "mathlib", "openqasm"]
  homepage    := "https://github.com/akkeshavan/lean-qverify"
  license     := "MIT"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0-rc1"

lean_lib LeanQVerify where
  roots := #[`LeanQVerify]

-- CLI binary: reads a QASM file, outputs a JSON elaboration result.
lean_exe «lean-qverify-check» where
  root := `LeanQVerify.Main

-- Test suite: compiled and checked at elaboration time via #guard.
lean_lib LeanQVerifyTests where
  roots   := #[`TestParser, `TestElaborator, `TestCircuit, `TestQState]
  srcDir  := "tests/lean"
