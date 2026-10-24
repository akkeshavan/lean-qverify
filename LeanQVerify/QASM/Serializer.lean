import LeanQVerify.QASM.Elaborator

/-!
# Circuit Serializer

Converts a `QASMProgram` into a Lean 4 source string defining a `QCircuit n`
value.  The generated code can be type-checked by Lean's kernel.

Angles that are recognised rational multiples of π are emitted as exact
`Real.pi`-based expressions.  Unrecognised floats are emitted using
`floatToReal` (sorry-backed); callers should check `angleIsRecognised`.
-/

namespace LeanQVerify.QASM

open LeanQVerify

-- ---------------------------------------------------------------------------
-- Angle serialization
-- ---------------------------------------------------------------------------

/-- Serialise a Float angle as a Lean ℝ expression. -/
def serializeAngle (θ : Float) : String :=
  if floatEq θ 0.0           then "0"
  else if floatEq θ fpi      then "Real.pi"
  else if floatEq θ (-fpi)   then "(-Real.pi)"
  else if floatEq θ (fpi/2)  then "(Real.pi / 2)"
  else if floatEq θ (-fpi/2) then "(-(Real.pi / 2))"
  else if floatEq θ (fpi/3)  then "(Real.pi / 3)"
  else if floatEq θ (-fpi/3) then "(-(Real.pi / 3))"
  else if floatEq θ (fpi/4)  then "(Real.pi / 4)"
  else if floatEq θ (-fpi/4) then "(-(Real.pi / 4))"
  else if floatEq θ (2*fpi/3)  then "(2 * Real.pi / 3)"
  else if floatEq θ (-2*fpi/3) then "(-(2 * Real.pi / 3))"
  else if floatEq θ (3*fpi/4)  then "(3 * Real.pi / 4)"
  else if floatEq θ (-3*fpi/4) then "(-(3 * Real.pi / 4))"
  else if floatEq θ (fpi/6)  then "(Real.pi / 6)"
  else if floatEq θ (-fpi/6) then "(-(Real.pi / 6))"
  else if floatEq θ (fpi/8)  then "(Real.pi / 8)"
  else if floatEq θ (-fpi/8) then "(-(Real.pi / 8))"
  else if floatEq θ (3*fpi/8)  then "(3 * Real.pi / 8)"
  else if floatEq θ (-3*fpi/8) then "(-(3 * Real.pi / 8))"
  else if floatEq θ (5*fpi/8)  then "(5 * Real.pi / 8)"
  else if floatEq θ (-5*fpi/8) then "(-(5 * Real.pi / 8))"
  else if floatEq θ (7*fpi/8)  then "(7 * Real.pi / 8)"
  else if floatEq θ (-7*fpi/8) then "(-(7 * Real.pi / 8))"
  else if floatEq θ (2*fpi)   then "(2 * Real.pi)"
  else if floatEq θ (-2*fpi)  then "(-(2 * Real.pi))"
  else if floatEq θ (3*fpi/2)  then "(3 * Real.pi / 2)"
  else if floatEq θ (-3*fpi/2) then "(-(3 * Real.pi / 2))"
  else s!"(floatToReal {θ})"

-- ---------------------------------------------------------------------------
-- Qubit and gate serialization
-- ---------------------------------------------------------------------------

private def serializeQubit (i : Nat) : String :=
  s!"⟨{i}, by decide⟩"

private def serializeGateApp (n : Nat) (m : RegMap) (g : GateApp) : Option String :=
  let res1 (r : QubitRef) : Option String :=
    resolveQubit m r >>= fun i => some (serializeQubit i)
  let res2 (r1 r2 : QubitRef) : Option (String × String) := do
    let s1 ← res1 r1; let s2 ← res1 r2; return (s1, s2)
  let res3 (r1 r2 r3 : QubitRef) : Option (String × String × String) := do
    let s1 ← res1 r1; let s2 ← res1 r2; let s3 ← res1 r3; return (s1, s2, s3)
  match g with
  | .h    q       => res1 q >>= fun i => some s!"(.H {i})"
  | .x    q       => res1 q >>= fun i => some s!"(.X {i})"
  | .y    q       => res1 q >>= fun i => some s!"(.Y {i})"
  | .z    q       => res1 q >>= fun i => some s!"(.Z {i})"
  | .s    q       => res1 q >>= fun i => some s!"(.S {i})"
  | .t    q       => res1 q >>= fun i => some s!"(.T {i})"
  | .rx   θ q     => res1 q >>= fun i => some s!"(.RX {serializeAngle θ} {i})"
  | .ry   θ q     => res1 q >>= fun i => some s!"(.RY {serializeAngle θ} {i})"
  | .rz   θ q     => res1 q >>= fun i => some s!"(.RZ {serializeAngle θ} {i})"
  | .cx   c t     => res2 c t >>= fun (ci, ti) => some s!"(.CNOT {ci} {ti})"
  | .cz   c t     => res2 c t >>= fun (ci, ti) => some s!"(.CZ {ci} {ti})"
  | .swap i j     => res2 i j >>= fun (ii, ji) => some s!"(.SWAP {ii} {ji})"
  | .ccx  c1 c2 t => res3 c1 c2 t >>= fun (c1i, c2i, ti) => some s!"(.CCX {c1i} {c2i} {ti})"
  | .u3   θ φ lam q => res1 q >>= fun i =>
      some s!"(.U3 {serializeAngle θ} {serializeAngle φ} {serializeAngle lam} {i})"
  | .ch   c t     => res2 c t >>= fun (ci, ti) => some s!"(.CH {ci} {ti})"
  | .cy   c t     => res2 c t >>= fun (ci, ti) => some s!"(.CY {ci} {ti})"
  | .cp   θ c t   => res2 c t >>= fun (ci, ti) =>
      some s!"(.CP {serializeAngle θ} {ci} {ti})"
  | .crz  θ c t   => res2 c t >>= fun (ci, ti) =>
      some s!"(.CRZ {serializeAngle θ} {ci} {ti})"
  | .rzz  θ i j   => res2 i j >>= fun (ii, ji) =>
      some s!"(.RZZ {serializeAngle θ} {ii} {ji})"
  | .rxx  θ i j   => res2 i j >>= fun (ii, ji) =>
      some s!"(.RXX {serializeAngle θ} {ii} {ji})"
  | .ryy  θ i j   => res2 i j >>= fun (ii, ji) =>
      some s!"(.RYY {serializeAngle θ} {ii} {ji})"
  | .skipped _    => none

-- ---------------------------------------------------------------------------
-- Full circuit serialization
-- ---------------------------------------------------------------------------

/-- Serialise a QASMProgram as a Lean `noncomputable def` for a `QCircuit n`.
    `defName` is the Lean identifier for the generated definition. -/
def serializeCircuit (prog : QASMProgram) (defName : String) : String :=
  let n := totalQubits prog.registers
  let m := buildRegMap prog.registers
  let gateStrs := prog.gates.filterMap (serializeGateApp n m)
  -- Build the cons chain using <| so each .cons gets exactly two arguments:
  --   .cons g1 <| .cons g2 <| ... <| .empty
  -- <| has very low right-associative precedence, so this parses correctly.
  let body := gateStrs.foldr (fun g acc => s!"  .cons {g} <|\n{acc}") "  .empty\n"
  s!"private noncomputable def {defName} : QCircuit {n} :=\n{body}"

end LeanQVerify.QASM
