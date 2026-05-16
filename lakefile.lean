import Lake
open Lake DSL

package «lean-qverify» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib LeanQVerify where
  roots := #[`LeanQVerify]

-- The verifier executable: reads a QASM file, outputs a JSON result.
lean_exe «lean-qverify-check» where
  root := `LeanQVerify.Main

-- Test library: all files under tests/lean/ are compiled and checked.
-- #guard and example statements run at elaboration time.
lean_lib LeanQVerifyTests where
  roots   := #[`TestParser, `TestElaborator, `TestCircuit, `TestQState]
  srcDir  := "tests/lean"
