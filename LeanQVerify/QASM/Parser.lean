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
  -- Extended gate set (Phase 2)
  | u3   : Float → Float → Float → QubitRef → GateApp   -- U3(θ,φ,λ)
  | ch   : QubitRef → QubitRef → GateApp                 -- Controlled-H
  | cy   : QubitRef → QubitRef → GateApp                 -- Controlled-Y
  | cp   : Float → QubitRef → QubitRef → GateApp         -- Controlled-phase(θ)
  | crz  : Float → QubitRef → QubitRef → GateApp         -- Controlled-Rz(θ)
  | rzz  : Float → QubitRef → QubitRef → GateApp         -- Rzz(θ)
  | rxx  : Float → QubitRef → QubitRef → GateApp         -- Rxx(θ)
  | ryy  : Float → QubitRef → QubitRef → GateApp         -- Ryy(θ)
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

private structure ParseState where
  src  : String
  pos  : Nat

private abbrev Parser (α : Type) := ParseState → Except String (α × ParseState)

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
        -- Handle optional exponent: e±N or E±N
        let baseVal := strToFloat intPart fracPart
        match peek s2 with
        | some 'e' | some 'E' =>
          let s3 := advance s2
          let (negExp, s4) := match peek s3 with
            | some '-' => (true,  advance s3)
            | some '+' => (false, advance s3)
            | _        => (false, s3)
          let (expDigits, s5) := readWhile Char.isDigit s4
          if expDigits.isEmpty then some (baseVal, s2)
          else
            let exp := expDigits.toNat!
            let factor := (List.range exp).foldl (fun acc _ => acc * 10.0) 1.0
            some (if negExp then baseVal / factor else baseVal * factor, s5)
        | _ => some (baseVal, s2)
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

-- Read a comma-separated list of floats (recursive, terminates when no float is found).
private partial def readFloatListAux (st : ParseState) (acc : List Float) :
    List Float × ParseState :=
  match readFloat st with
  | none        => (acc.reverse, st)
  | some (f, st') =>
    let st'' := skipNoise st'
    if peek st'' = some ','
    then readFloatListAux (skipNoise (advance st'')) (f :: acc)
    else ((f :: acc).reverse, st'')

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
    | "measure" => (none, skipToSemicolon s1)        -- measurements, ignore
    | "barrier" => (none, skipToSemicolon s1)        -- barriers, ignore
    | "qubit" =>
      -- OpenQASM 3: qubit[n] name;
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
    | "qreg" =>
      -- OpenQASM 2.0: qreg name[n];
      let s1 := skipNoise s1
      match readIdent s1 with
      | none => (none, skipToSemicolon s1)
      | some (name, s2) =>
        let s2 := skipNoise s2
        match expectChar '[' s2 with
        | .error _ => (none, skipToSemicolon s2)
        | .ok (_, s3) =>
          match readNat (skipNoise s3) with
          | none => (none, skipToSemicolon s3)
          | some (size, s4) =>
            match expectChar ']' (skipNoise s4) with
            | .error _ => (none, skipToSemicolon s4)
            | .ok (_, s5) =>
              (some (.inr (.inl ⟨name, size⟩)), skipToSemicolon s5)
    | gateName =>
      -- Gate application
      let s1 := skipNoise s1
      -- Parse angle list: gateName(a) or gateName(a,b,c) or gateName (no parens)
      let (angles, s2) :=
        if peek s1 = some '('
        then
          let s1' := skipNoise (advance s1)
          let (fs, sAfter) := readFloatListAux s1' []
          match expectChar ')' (skipNoise sAfter) with
          | .ok (_, sAfterParen) => (fs, skipNoise sAfterParen)
          | .error _             => ([], s1)
        else ([], s1)
      -- Parse qubit arguments
      let (qubits, s3) := parseQubitsAux s2 []
      let s4 := skipToSemicolon s3
      let gate : Option GateApp := match gateName, qubits, angles with
        | "h",    [q],          []            => some (.h q)
        | "x",    [q],          []            => some (.x q)
        | "y",    [q],          []            => some (.y q)
        | "z",    [q],          []            => some (.z q)
        | "s",    [q],          []            => some (.s q)
        | "t",    [q],          []            => some (.t q)
        -- S†: RZ(-π/2); T†: RZ(-π/4)  (OpenQASM 2.0 adjoint gates)
        | "sdg",  [q],          []            => some (.rz (-1.5707963267948966) q)
        | "tdg",  [q],          []            => some (.rz (-0.7853981633974483) q)
        -- id / nop: identity gate, skip (no semantic effect)
        | "id",   _,            _             => none
        | "cx",   [c, t],       []            => some (.cx c t)
        | "cnot", [c, t],       []            => some (.cx c t)
        | "cz",   [c, t],       []            => some (.cz c t)
        | "swap", [i, j],       []            => some (.swap i j)
        | "ccx",  [c1, c2, t],  []            => some (.ccx c1 c2 t)
        | "toffoli", [c1,c2,t], []            => some (.ccx c1 c2 t)
        | "rx",   [q],          [θ]           => some (.rx θ q)
        | "ry",   [q],          [θ]           => some (.ry θ q)
        | "rz",   [q],          [θ]           => some (.rz θ q)
        -- u1/p: phase gate = RZ(λ); u2/u3: universal gates
        | "u1",   [q],          [θ]           => some (.rz θ q)
        | "p",    [q],          [θ]           => some (.rz θ q)
        | "u2",   [q],          [φ, lam]      => some (.u3 1.5707963267948966 φ lam q)
        | "u3",   [q],          [θ, φ, lam]   => some (.u3 θ φ lam q)
        -- Controlled single-qubit gates
        | "ch",   [c, t],       []            => some (.ch c t)
        | "cy",   [c, t],       []            => some (.cy c t)
        -- Controlled rotation gates
        | "cp",   [c, t],       [θ]           => some (.cp θ c t)
        | "crz",  [c, t],       [θ]           => some (.crz θ c t)
        -- Two-qubit rotation gates
        | "rzz",  [i, j],       [θ]           => some (.rzz θ i j)
        | "rxx",  [i, j],       [θ]           => some (.rxx θ i j)
        | "ryy",  [i, j],       [θ]           => some (.ryy θ i j)
        | name,   _,            _             => some (.skipped name)
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
