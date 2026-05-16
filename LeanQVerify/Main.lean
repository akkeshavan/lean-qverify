import LeanQVerify.QASM.Elaborator

/-!
# lean-qverify-check  —  CLI entry point

Usage:
    lean-qverify-check <circuit.qasm>

Reads an OpenQASM 3 file, elaborates it into a `QCircuit n`, and prints:
  - The number of qubits and gates
  - Any parse / elaboration warnings
  - A JSON summary written to stdout so the Python bridge can consume it

Exit codes:
  0  success (file parsed and elaborated; warnings are non-fatal)
  1  usage error
  2  file not found / read error
-/

-- ---------------------------------------------------------------------------
-- JSON serialisation  (minimal hand-rolled; Lean's Std has Json but we keep
-- this dependency-free for the Phase 1 build)
-- ---------------------------------------------------------------------------

namespace LeanQVerify.QASM

private def escapeJson (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _    => acc.push c) ""

private def jsonStr (s : String) : String := "\"" ++ escapeJson s ++ "\""

private def jsonList (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

/-- Serialise an `ElabResult` to a minimal JSON object. -/
def toJson (r : ElabResult) : String :=
  let warnList := r.warnings.map jsonStr
  "{" ++
    "\"nQubits\":"  ++ toString r.nQubits ++ "," ++
    "\"nGates\":"   ++ toString r.nGates  ++ "," ++
    "\"warnings\":" ++ jsonList warnList  ++
  "}"

end LeanQVerify.QASM

open LeanQVerify.QASM in
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    -- Read the QASM file
    let source ← try
      IO.FS.readFile path
    catch e =>
      IO.eprintln s!"Error reading '{path}': {e}"
      IO.Process.exit 2
    let res := parseAndElaborate source
    -- Print JSON summary to stdout for the Python bridge
    IO.println (toJson res)
  | _ =>
    IO.eprintln "Usage: lean-qverify-check <circuit.qasm>"
    IO.Process.exit 1
