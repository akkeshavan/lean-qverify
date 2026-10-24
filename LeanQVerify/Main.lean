import LeanQVerify.QASM.Elaborator
import LeanQVerify.QASM.Serializer

/-!
# lean-qverify-check  —  CLI entry point

## Usage

```
lean-qverify-check <circuit.qasm>
```
Parse and elaborate a QASM file; print a JSON summary.

```
lean-qverify-check --emit-lean <circuit.qasm> [<defName>]
```
Emit a Lean `noncomputable def` for the circuit.  `defName` defaults to
`importedCircuit`.  Output is valid Lean 4 source that can be imported and
used in proofs.

## Exit codes

  0  success
  1  usage error
  2  file not found / read error
-/

-- ---------------------------------------------------------------------------
-- JSON serialisation  (minimal hand-rolled)
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

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

open LeanQVerify.QASM in
def main (args : List String) : IO Unit := do
  match args with
  -- Default mode: parse and report JSON
  | [path] => do
    let source ← try IO.FS.readFile path
      catch e => IO.eprintln s!"Error reading '{path}': {e}"; IO.Process.exit 2
    let res := parseAndElaborate source
    IO.println (toJson res)

  -- Emit-lean mode: output a Lean def for the circuit
  | ["--emit-lean", path] =>
    runEmitLean path "importedCircuit"
  | ["--emit-lean", path, defName] =>
    runEmitLean path defName

  | _ =>
    IO.eprintln "Usage:"
    IO.eprintln "  lean-qverify-check <circuit.qasm>"
    IO.eprintln "  lean-qverify-check --emit-lean <circuit.qasm> [<defName>]"
    IO.Process.exit 1

where
  runEmitLean (path defName : String) : IO Unit := do
    let source ← try IO.FS.readFile path
      catch e => IO.eprintln s!"Error reading '{path}': {e}"; IO.Process.exit 2
    let prog := LeanQVerify.QASM.parse source
    IO.println (LeanQVerify.QASM.serializeCircuit prog defName)
