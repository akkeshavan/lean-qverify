import Lake
open Lake DSL

package «lean-qverify-book» where
  version := v!"0.1.0"

-- The book depends on the lean-qverify library in the parent directory.
-- If you cloned the repository, this path already exists.
require «lean-qverify» from ".."

lean_lib Book where
  roots := #[`Book]
