import Lake
open Lake DSL

package «lean-qverify-theorems» where
  version := v!"0.1.0"

-- Depend on the lean-qverify library in the parent directory.
-- Anyone who clones the repo already has the parent available.
require «lean-qverify» from ".."

-- One library target per circuit family, matching the paper's theorem groups.
lean_lib Theorems where
  roots := #[`BellState, `GHZTeleportation, `HEA, `GateAlgebra, `Grover]
