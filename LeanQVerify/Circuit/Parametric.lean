import LeanQVerify.Circuit.QCircuit
import LeanQVerify.Spec.CircuitSpec

/-!
# Parametric Circuit Families

Defines `QFamily`, the `ghzCircuit` and `bvCircuit` families, and proves
gate-count theorems by structural induction.

Key results:
- `ghzCircuit n : QCircuit (n+1)` — H on qubit 0, then CNOT(0,k) for k=1..n
- `ghzCircuit_gateCount n` — exactly n+1 gates (inductive proof)
- `ghzCircuit_cnotCount n` — exactly n CNOT gates (inductive proof)
- `bvOracle n s : QCircuit (n+1)` — CNOT oracle for Bernstein-Vazirani
- `bvCircuit n s : QCircuit (n+1)` — full BV circuit (H⊗n, ancilla, oracle, H⊗n)
- `bvOracle_cnotCount_le n s` — at most n CNOTs in the oracle (inductive proof)
-/

namespace LeanQVerify

open QCircuit CircuitSpec

-- ---------------------------------------------------------------------------
-- Circuit embedding: QCircuit n → QCircuit (n+1)
-- ---------------------------------------------------------------------------

/-- Cast a gate's qubit indices from Fin n to Fin (n+1) via Fin.castSucc. -/
private def Gate.castSucc {n : ℕ} : Gate n → Gate (n + 1)
  | .H  i        => .H  i.castSucc
  | .X  i        => .X  i.castSucc
  | .Y  i        => .Y  i.castSucc
  | .Z  i        => .Z  i.castSucc
  | .S  i        => .S  i.castSucc
  | .T  i        => .T  i.castSucc
  | .RX θ i      => .RX θ i.castSucc
  | .RY θ i      => .RY θ i.castSucc
  | .RZ θ i      => .RZ θ i.castSucc
  | .CNOT c t    => .CNOT c.castSucc t.castSucc
  | .CZ  c t     => .CZ  c.castSucc t.castSucc
  | .SWAP i j    => .SWAP i.castSucc j.castSucc
  | .CCX c1 c2 t => .CCX c1.castSucc c2.castSucc t.castSucc
  | .U3 θ φ l i  => .U3 θ φ l i.castSucc
  | .CH  c t     => .CH  c.castSucc t.castSucc
  | .CY  c t     => .CY  c.castSucc t.castSucc
  | .CP  θ c t   => .CP  θ c.castSucc t.castSucc
  | .CRZ θ c t   => .CRZ θ c.castSucc t.castSucc
  | .RZZ θ i j   => .RZZ θ i.castSucc j.castSucc
  | .RXX θ i j   => .RXX θ i.castSucc j.castSucc
  | .RYY θ i j   => .RYY θ i.castSucc j.castSucc

/-- Embed a circuit for n qubits into one for n+1 qubits (new qubit is unused). -/
def QCircuit.castSucc {n : ℕ} : QCircuit n → QCircuit (n + 1)
  | .empty     => .empty
  | .cons g c  => .cons g.castSucc c.castSucc

-- ---------------------------------------------------------------------------
-- Shared predicate: is the gate a CNOT?
-- ---------------------------------------------------------------------------

-- We use an explicit def so proofs can unfold it and match syntactically.
private def cnotPred {n : ℕ} (g : Gate n) : Bool :=
  match g with | .CNOT .. => true | _ => false

-- Key facts about cnotPred (by definition).
private theorem cnotPred_CNOT {n : ℕ} (c t : Fin n) : cnotPred (.CNOT c t) = true := rfl
private theorem cnotPred_H    {n : ℕ} (i : Fin n) : cnotPred (.H i) = false := rfl

-- Gate.castSucc maps CNOT ↔ CNOT, so cnotPred is preserved.
private theorem castSucc_cnotPred {n : ℕ} (g : Gate n) :
    cnotPred g.castSucc = cnotPred g := by
  unfold cnotPred; cases g <;> simp [Gate.castSucc]

-- ---------------------------------------------------------------------------
-- Size and count preserved by castSucc
-- ---------------------------------------------------------------------------

@[simp]
private theorem castSucc_size {n : ℕ} (c : QCircuit n) : c.castSucc.size = c.size := by
  induction c with
  | empty     => rfl
  | cons _ _ ih => simp [QCircuit.castSucc, size, ih]

private theorem castSucc_countCNOT {n : ℕ} (c : QCircuit n) :
    countGates cnotPred c.castSucc = countGates cnotPred c := by
  induction c with
  | empty     => rfl
  | cons g c ih =>
    simp only [QCircuit.castSucc, countGates, castSucc_cnotPred g, ih]

-- ---------------------------------------------------------------------------
-- countGates is additive over append.
-- ---------------------------------------------------------------------------

theorem countGates_append {n : ℕ} (pred : Gate n → Bool) (c₁ c₂ : QCircuit n) :
    countGates pred (c₁.append c₂) = countGates pred c₁ + countGates pred c₂ := by
  induction c₁ with
  | empty       => simp [QCircuit.append, countGates]
  | cons _ _ ih => simp [QCircuit.append, countGates, ih, Nat.add_assoc]

-- ---------------------------------------------------------------------------
-- QFamily: a parameterised family of quantum circuits
-- ---------------------------------------------------------------------------

/-- A family of circuits where the qubit count varies as f(n). -/
def QFamily (f : ℕ → ℕ) := (n : ℕ) → QCircuit (f n)

-- ---------------------------------------------------------------------------
-- GHZ state preparation circuit (n+1 qubits)
-- ---------------------------------------------------------------------------

/-- CNOT entangling tail for GHZ within an (n+2)-qubit circuit.
    Contains CNOT(0, 1), CNOT(0, 2), ..., CNOT(0, n+1). -/
private def ghzCNOTs : (n : ℕ) → QCircuit (n + 2)
  | 0     => .cons (.CNOT ⟨0, by omega⟩ ⟨1, by omega⟩) .empty
  | n + 1 => .cons (.CNOT ⟨0, by omega⟩ ⟨n + 2, by omega⟩) (ghzCNOTs n).castSucc

/-- GHZ preparation for n+1 qubits: H on qubit 0, then CNOT(0,k) for k=1..n. -/
def ghzCircuit : (n : ℕ) → QCircuit (n + 1)
  | 0     => .cons (.H ⟨0, by omega⟩) .empty
  | n + 1 => .cons (.H ⟨0, by omega⟩) (ghzCNOTs n)

/-- The GHZ family: `ghzFamily n` is the (n+1)-qubit GHZ preparation circuit. -/
def ghzFamily : QFamily (· + 1) := ghzCircuit

-- ---------------------------------------------------------------------------
-- GHZ gate count theorems (proved by structural induction)
-- ---------------------------------------------------------------------------

-- (i) Size of the CNOT tail — straightforward by induction.
private theorem ghzCNOTs_size (n : ℕ) : (ghzCNOTs n).size = n + 1 := by
  induction n with
  | zero    => rfl
  | succ n ih => simp only [ghzCNOTs, size, castSucc_size, ih]; omega

/-- GHZ circuit for n+1 qubits has exactly n+1 gates. -/
theorem ghzCircuit_gateCount (n : ℕ) : ghzCircuit n ⊨ totalGates (n + 1) := by
  simp only [satisfies, totalGates]
  have heq : ∀ {m : ℕ} (c : QCircuit m), countGates (fun _ => true) c = c.size := by
    intro m c; induction c with
    | empty      => rfl
    | cons _ _ ih => simp [countGates, size, ih]
  cases n with
  | zero    => simp [ghzCircuit, size, heq]
  | succ n  => simp only [ghzCircuit, heq, size, ghzCNOTs_size]; omega

-- (ii) CNOT count — need castSucc_countCNOT to track CNOTs through embedding.
-- We use `show` to exploit that cnotPred reduces definitionally on known constructors.
private theorem ghzCNOTs_cnotCount (n : ℕ) :
    countGates cnotPred (ghzCNOTs n) = n + 1 := by
  induction n with
  | zero    => rfl  -- ghzCNOTs 0 = cons (CNOT 0 1) empty; cnotPred reduces to 1
  | succ n ih =>
    -- ghzCNOTs (n+1) = cons (CNOT 0 (n+2)) (ghzCNOTs n).castSucc
    -- cnotPred (CNOT ..) = true, so this cons adds 1 to the count
    -- castSucc_countCNOT gives the same count in the embedded circuit
    show 1 + countGates cnotPred (ghzCNOTs n).castSucc = n + 1 + 1
    rw [castSucc_countCNOT, ih]; omega

/-- GHZ circuit for n+1 qubits has exactly n CNOT gates. -/
theorem ghzCircuit_cnotCount (n : ℕ) : ghzCircuit n ⊨ maxCNOTs n := by
  simp only [satisfies, maxCNOTs]
  -- The lambda in maxCNOTs is definitionally cnotPred; use show to exploit this.
  show countGates cnotPred (ghzCircuit n) ≤ n
  cases n with
  | zero    => simp [ghzCircuit, countGates, cnotPred]
  | succ n  =>
    -- ghzCircuit (n+1) = cons (H 0) (ghzCNOTs n); cnotPred (H ..) = false definitionally
    show 0 + countGates cnotPred (ghzCNOTs n) ≤ n + 1
    simp only [Nat.zero_add]
    exact Nat.le_of_eq (ghzCNOTs_cnotCount n)

-- ---------------------------------------------------------------------------
-- Bernstein-Vazirani circuit (n+1 qubits: n query + 1 ancilla)
-- ---------------------------------------------------------------------------

/-- BV oracle, recursively defined: adds CNOT(k, n) when s[k] = true, k=0..m-1. -/
private def bvOracleAux (n : ℕ) (s : Fin n → Bool) : (m : ℕ) → QCircuit (n + 1)
  | 0     => .empty
  | m + 1 =>
      if hm : m < n then
        let prev := bvOracleAux n s m
        if s ⟨m, hm⟩ then .cons (.CNOT ⟨m, Nat.lt_succ_of_lt hm⟩ ⟨n, Nat.lt_succ_self n⟩) prev
                      else prev
      else bvOracleAux n s m

/-- BV oracle: CNOT(i, n) for each query qubit i where s[i] = true. -/
def bvOracle (n : ℕ) (s : Fin n → Bool) : QCircuit (n + 1) := bvOracleAux n s n

/-- H layer on query qubits 0..m-1 within an (n+1)-qubit circuit. -/
private def hLayerAux (n : ℕ) : (m : ℕ) → QCircuit (n + 1)
  | 0     => .empty
  | m + 1 =>
      if hm : m < n then .cons (.H ⟨m, Nat.lt_succ_of_lt hm⟩) (hLayerAux n m)
      else hLayerAux n m

private def hQueryLayer (n : ℕ) : QCircuit (n + 1) := hLayerAux n n

/-- Full Bernstein-Vazirani circuit.
    n+1 qubits: query 0..n-1, ancilla at index n.
    Structure: H⊗n ∥ X(n);H(n) → oracle → H⊗n. -/
def bvCircuit (n : ℕ) (s : Fin n → Bool) : QCircuit (n + 1) :=
  hQueryLayer n ++
  .cons (.H ⟨n, Nat.lt_succ_self n⟩) (.cons (.X ⟨n, Nat.lt_succ_self n⟩) .empty) ++
  bvOracle n s ++
  hQueryLayer n

/-- The BV family with a given hidden-string generator. -/
def bvFamily (s : (n : ℕ) → Fin n → Bool) : QFamily (· + 1) := fun n => bvCircuit n (s n)

-- ---------------------------------------------------------------------------
-- BV oracle CNOT count (proved by induction on m)
-- ---------------------------------------------------------------------------

private theorem bvOracleAux_cnotCount (n : ℕ) (s : Fin n → Bool) (m : ℕ) :
    countGates cnotPred (bvOracleAux n s m) ≤ m := by
  induction m with
  | zero    => simp [bvOracleAux, countGates]
  | succ m ih =>
    unfold bvOracleAux
    split_ifs with hlt hs
    · -- adds CNOT: cnotPred (CNOT ..) = true, so count increases by 1
      show 1 + countGates cnotPred (bvOracleAux n s m) ≤ m + 1
      omega
    · exact Nat.le_succ_of_le ih
    · exact Nat.le_succ_of_le ih

/-- The BV oracle uses at most n CNOT gates. -/
theorem bvOracle_cnotCount_le (n : ℕ) (s : Fin n → Bool) :
    bvOracle n s ⊨ maxCNOTs n := by
  simp only [satisfies, maxCNOTs]
  -- The lambda in maxCNOTs is definitionally cnotPred; use show to exploit this.
  show countGates cnotPred (bvOracle n s) ≤ n
  unfold bvOracle
  exact bvOracleAux_cnotCount n s n

end LeanQVerify
