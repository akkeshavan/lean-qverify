import Mathlib.Data.String.Basic

/-!
# OpenQASM 3 Subset Parser

Parses the subset of OpenQASM 3 that lean-qverify supports:
  - `OPENQASM 3;` header
  - `include "stdgates.inc";` (ignored)
  - `qubit[n] name;` register declarations
  - Gate applications: `h q[i];`, `cx q[c], q[t];`, `rx(theta) q[i];` etc.

Unsupported constructs produce a warning and are skipped rather than failing.
The parser is NOT formally verified — it is a trusted bridge component.
-/

namespace LeanQVerify.QASM

-- ---------------------------------------------------------------------------
-- AST types
-- ---------------------------------------------------------------------------

/-- A qubit reference: register name and index. -/
structure QubitRef where
  reg   : String
  index : ℕ
  deriving Repr, BEq, Inhabited

/-- A parsed gate application. -/
inductive GateApp : Type where
  | h    : QubitRef → GateApp
  | x    : QubitRef → GateApp
  | y    : QubitRef → GateApp
  | z    : QubitRef → GateApp
  | s    : QubitRef → GateApp
  | t    : QubitRef → GateApp
  | cx   : QubitRef → QubitRef → GateApp
  | cz   : QubitRef → QubitRef → GateApp
  | swap : QubitRef → QubitRef → GateApp
  | ccx  : QubitRef → QubitRef → QubitRef → GateApp
  | rx   : Float → QubitRef → GateApp
  | ry   : Float → QubitRef → GateApp
  | rz   : Float → QubitRef → GateApp
  | skipped : String → GateApp   -- unsupported gate, kept for warning
  deriving Repr, Inhabited

/-- A qubit register declaration. -/
structure RegDecl where
  name : String
  size : ℕ
  deriving Repr, Inhabited

/-- The full parsed program. -/
structure QASMProgram where
  registers : List RegDecl
  gates     : List GateApp
  warnings  : List String   -- unsupported constructs encountered
  deriving Repr, Nonempty

-- ---------------------------------------------------------------------------
-- Parser state and primitives
-- ---------------------------------------------------------------------------

structure ParseState where
  src  : String
  pos  : Nat

abbrev Parser (α : Type) := ParseState → Except String (α × ParseState)

private def peek (s : ParseState) : Option Char :=
  s.src.get? ⟨s.pos⟩

private def advance (s : ParseState) : ParseState :=
  { s with pos := s.pos + 1 }

-- ---------------------------------------------------------------------------
-- Recursive helpers as top-level partial defs (parser is a trusted bridge)
-- ---------------------------------------------------------------------------

private partial def skipWhitespaceAux (st : ParseState) : ParseState :=
  match peek st with
  | some c => if c.isWhitespace then skipWhitespaceAux (advance st) else st
  | none   => st

private def skipWhitespace (s : ParseState) : ParseState := skipWhitespaceAux s

private partial def skipLineCommentAux (st : ParseState) : ParseState :=
  match peek st with
  | some '\n' => advance st
  | some _    => skipLineCommentAux (advance st)
  | none      => st

private def skipLineComment (s : ParseState) : ParseState := skipLineCommentAux s

private partial def skipNoise (s : ParseState) : ParseState :=
  let s' := skipWhitespace s
  match peek s' with
  | some '/' =>
    let s'' := advance s'
    match peek s'' with
    | some '/' => skipNoise (skipLineComment (advance s''))
    | _        => s'
  | _ => s'

private partial def readWhileAux (pred : Char → Bool) (st : ParseState) (acc : String) :
    String × ParseState :=
  match peek st with
  | some c => if pred c then readWhileAux pred (advance st) (acc.push c) else (acc, st)
  | none   => (acc, st)

private def readWhile (pred : Char → Bool) (s : ParseState) : String × ParseState :=
  readWhileAux pred s ""

private def readIdent (s : ParseState) : Option (String × ParseState) :=
  match peek s with
  | some c =>
    if c.isAlpha || c = '_' then
      let (ident, s') := readWhile (fun c => c.isAlpha || c.isDigit || c = '_') s
      some (ident, s')
    else none
  | none => none

private def readNat (s : ParseState) : Option (ℕ × ParseState) :=
  let (digits, s') := readWhile Char.isDigit s
  if digits.isEmpty then none
  else some (digits.toNat!, s')

/-- Convert integer and fractional digit strings to a Float. -/
private def strToFloat (intPart fracPart : String) : Float :=
  let intF : Float := Float.ofScientific intPart.toNat! false 0
  let (fracF, _) := fracPart.foldl (fun (acc : Float × Float) c =>
    let digit := Float.ofScientific (c.toNat - 48) false 0
    (acc.1 + digit / acc.2, acc.2 * 10.0)) (0.0, 10.0)
  intF + fracF

private partial def readFloat (s : ParseState) : Option (Float × ParseState) :=
  match peek s with
  | some 'p' =>
    -- Try to parse 'pi' or 'pi/N' or 'pi*N'
    let s1 := advance s
    match peek s1 with
    | some 'i' =>
      let s2 := advance s1
      let pi := Float.ofScientific 31415926535 true 10  -- π ≈ 3.1415...
      match peek s2 with
      | some '/' =>
        let s3 := skipWhitespace (advance s2)
        match readFloat s3 with
        | some (d, s4) => some (pi / d, s4)
        | none => some (pi, s2)
      | some '*' =>
        let s3 := skipWhitespace (advance s2)
        match readFloat s3 with
        | some (d, s4) => some (pi * d, s4)
        | none => some (pi, s2)
      | _ => some (pi, s2)
    | _ => none
  | some '-' =>
    match readFloat (advance s) with
    | some (f, s') => some (-f, s')
    | none => none
  | _ =>
    let (intPart, s1) := readWhile Char.isDigit s
    if intPart.isEmpty then none
    else
      match peek s1 with
      | some '.' =>
        let (fracPart, s2) := readWhile Char.isDigit (advance s1)
        some (strToFloat intPart fracPart, s2)
      | _ => some (strToFloat intPart "", s1)

private def expectChar (c : Char) : Parser Unit := fun s =>
  let s' := skipNoise s
  match peek s' with
  | some ch => if ch = c then .ok ((), advance s') else .error s!"expected '{c}', got '{ch}'"
  | none    => .error s!"expected '{c}', got end of input"

private partial def expectStrAux (str : String) (st : ParseState) (idx : Nat) :
    Except String ParseState :=
  if idx = str.length then .ok st
  else match peek st with
    | some c =>
      if c = str.get ⟨idx⟩
      then expectStrAux str (advance st) (idx + 1)
      else .error s!"expected '{str}'"
    | none => .error s!"expected '{str}', got end of input"

private def expectStr (str : String) : Parser Unit := fun s =>
  (expectStrAux str s 0).map ((), ·)

-- ---------------------------------------------------------------------------
-- Parse a qubit reference: name[index]
-- ---------------------------------------------------------------------------

private def parseQubitRef : Parser QubitRef := fun s =>
  let s := skipNoise s
  match readIdent s with
  | none => .error "expected qubit register name"
  | some (name, s1) =>
    let s1 := skipNoise s1
    match expectChar '[' s1 with
    | .error e => .error e
    | .ok (_, s2) =>
      match readNat (skipNoise s2) with
      | none => .error "expected qubit index"
      | some (idx, s3) =>
        match expectChar ']' (skipNoise s3) with
        | .error e => .error e
        | .ok (_, s4) => .ok (⟨name, idx⟩, s4)

-- ---------------------------------------------------------------------------
-- Parse a single statement (gate application or declaration)
-- ---------------------------------------------------------------------------

private partial def skipToSemicolonAux (st : ParseState) : ParseState :=
  match peek st with
  | some ';' => advance st
  | some _   => skipToSemicolonAux (advance st)
  | none     => st

private def skipToSemicolon (s : ParseState) : ParseState := skipToSemicolonAux s

/-- Parse a comma-separated list of qubit references. -/
private partial def parseQubitsAux (st : ParseState) (acc : List QubitRef) :
    List QubitRef × ParseState :=
  match parseQubitRef st with
  | .error _ => (acc.reverse, st)
  | .ok (q, st') =>
    let st'' := skipNoise st'
    if peek st'' = some ','
    then parseQubitsAux (skipNoise (advance st'')) (q :: acc)
    else (List.reverse (q :: acc), st'')

private def parseStatement (s : ParseState) :
    Option (GateApp ⊕ RegDecl ⊕ String) × ParseState :=
  let s := skipNoise s
  match readIdent s with
  | none => (none, s)
  | some (kw, s1) =>
    match kw with
    | "OPENQASM" => (none, skipToSemicolon s1)
    | "include"  => (none, skipToSemicolon s1)
    | "bit" | "creg" => (none, skipToSemicolon s1)  -- classical bits, ignore
    | "qubit" =>
      -- qubit[n] name;
      let s1 := skipNoise s1
      match expectChar '[' s1 with
      | .error _ => (none, skipToSemicolon s1)
      | .ok (_, s2) =>
        match readNat (skipNoise s2) with
        | none => (none, skipToSemicolon s2)
        | some (size, s3) =>
          match expectChar ']' (skipNoise s3) with
          | .error _ => (none, skipToSemicolon s3)
          | .ok (_, s4) =>
            let s4 := skipNoise s4
            match readIdent s4 with
            | none => (none, skipToSemicolon s4)
            | some (name, s5) =>
              (some (.inr (.inl ⟨name, size⟩)), skipToSemicolon s5)
    | gateName =>
      -- Gate application
      let s1 := skipNoise s1
      -- Check for angle parameter: gateName(theta) or gateName qubit
      let (maybeAngle, s2) :=
        if peek s1 = some '('
        then
          match readFloat (skipNoise (advance s1)) with
          | none => (none, s1)
          | some (f, sAfter) =>
            match expectChar ')' (skipNoise sAfter) with
            | .ok (_, sAfterParen) => (some f, skipNoise sAfterParen)
            | .error _ => (none, s1)
        else (none, s1)
      -- Parse qubit arguments
      let (qubits, s3) := parseQubitsAux s2 []
      let s4 := skipToSemicolon s3
      let gate : Option GateApp := match gateName, qubits, maybeAngle with
        | "h",    [q],       none  => some (.h q)
        | "x",    [q],       none  => some (.x q)
        | "y",    [q],       none  => some (.y q)
        | "z",    [q],       none  => some (.z q)
        | "s",    [q],       none  => some (.s q)
        | "t",    [q],       none  => some (.t q)
        | "cx",   [c, t],    none  => some (.cx c t)
        | "cnot", [c, t],    none  => some (.cx c t)
        | "cz",   [c, t],    none  => some (.cz c t)
        | "swap", [i, j],    none  => some (.swap i j)
        | "ccx",  [c1,c2,t], none  => some (.ccx c1 c2 t)
        | "rx",   [q],       some θ => some (.rx θ q)
        | "ry",   [q],       some θ => some (.ry θ q)
        | "rz",   [q],       some θ => some (.rz θ q)
        | name,   _,         _     => some (.skipped name)
      (gate.map .inl, s4)

-- ---------------------------------------------------------------------------
-- Top-level parser
-- ---------------------------------------------------------------------------

private partial def parseAux (s : ParseState) (regs : List RegDecl) (gates : List GateApp)
    (warnings : List String) : QASMProgram :=
  let s' := skipNoise s
  if s'.pos ≥ s'.src.length then
    { registers := regs.reverse, gates := gates.reverse, warnings := warnings.reverse }
  else
    match parseStatement s' with
    | (none, s'') =>
      if s''.pos = s'.pos then  -- no progress — skip one char to avoid loop
        parseAux (advance s'') regs gates warnings
      else
        parseAux s'' regs gates warnings
    | (some (.inl (.skipped name)), s'') =>
      parseAux s'' regs gates (s!"unsupported gate: {name}" :: warnings)
    | (some (.inl g), s'') =>
      parseAux s'' regs (g :: gates) warnings
    | (some (.inr (.inl r)), s'') =>
      parseAux s'' (r :: regs) gates warnings
    | (some (.inr (.inr _)), s'') =>
      parseAux s'' regs gates warnings

/-- Parse an OpenQASM 3 program string into a QASMProgram. -/
def parse (source : String) : QASMProgram :=
  parseAux ⟨source, 0⟩ [] [] []

end LeanQVerify.QASM
