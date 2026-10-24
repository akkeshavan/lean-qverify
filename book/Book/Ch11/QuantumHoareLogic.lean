import LeanQVerify.Foundation.HoareLogic

/-!
# Chapter 11 — Quantum Hoare Logic

Read `prose.md` alongside this file.

QHL adapts classical Hoare triples to quantum programs.
The triple {A} c {B} means: for any density operator ρ,
  tr(A · ρ) ≤ tr(B · (c.denote · ρ · c.denote†))
-/

open LeanQVerify QCircuit

-- ── 1. Quantum predicates ─────────────────────────────────────────────────────

-- A QPred n is a 2ⁿ×2ⁿ Hermitian matrix A with 0 ≤ A ≤ I in the Löwner order.
-- tr(A·ρ) gives the probability of observing A when the system is in state ρ.
#check @QPred

-- Two concrete predicates:
-- trivial: mat = 0.  tr(0·ρ) = 0 — never observed.
-- full:    mat = I.  tr(I·ρ) = tr(ρ) = 1 — always observed.
#check @QPred.trivial   -- QPred.trivial (n : ℕ) : QPred n
#check @QPred.full      -- QPred.full    (n : ℕ) : QPred n

-- ── 2. The Hoare triple ───────────────────────────────────────────────────────

-- HoareTriple A c B : for all density operators ρ with tr(ρ) = 1,
--   tr(A·ρ) ≤ tr(B · (c.denote · ρ · c.denote†))
#check @HoareTriple

-- ── 3. Skip rule ─────────────────────────────────────────────────────────────

-- {A} empty {A}: the empty circuit preserves the state.
theorem ex_skip (A : QPred 1) : HoareTriple A .empty A :=
  hoare_skip A

example (A : QPred 2) : HoareTriple A .empty A :=
  hoare_skip A

-- ── 4. Gate rule ─────────────────────────────────────────────────────────────

-- For a gate with matrix U satisfying U†U = I:
--   {U†·A·U} gate(U) {A}
-- QPred.conj A U hU constructs the pulled-back predicate U†·A·U.
#check @hoare_gate
#check @QPred.conj

-- ── 5. H gate triple ─────────────────────────────────────────────────────────

-- H is Hermitian (H† = H) and unitary (H·H = I), so H†·A·H = H·A·H.

private lemma H_gate1_unitary :
    (Gate.H (⟨0, by norm_num⟩ : Fin 1)).matrix.conjTranspose *
    (Gate.H (⟨0, by norm_num⟩ : Fin 1)).matrix = 1 := by
  -- simp reduces Gate.matrix and embedGate1; rw handles cross-Fin-type rewrites
  simp only [Gate.matrix, embedGate1_one_qubit]
  rw [H_mat_conjTranspose, H_mat_unitary]

-- For any QPred A, the Hoare triple for a single-qubit H gate:
theorem H_gate_triple (A : QPred 1) :
    HoareTriple
      (A.conj (Gate.H (⟨0, by norm_num⟩ : Fin 1)).matrix H_gate1_unitary)
      (ofGate (.H ⟨0, by norm_num⟩))
      A :=
  hoare_gate A (.H ⟨0, by norm_num⟩) H_gate1_unitary

-- ── 6. Sequential composition ─────────────────────────────────────────────────

-- {A} c₁ {B} and {B} c₂ {C} give {A} (c₁ ++ c₂) {C},
-- provided c₁ is unitary (c₁.denote† · c₁.denote = 1).
#check @hoare_seq

-- Walk-through: composing two H triples.
-- h₁ : {H·A·H} H {A}
-- h₂ : {H·(H·A·H)·H} H {H·A·H}
-- hoare_seq gives: {H·(H·A·H)·H} H;H {A}
-- Since H·H = I, the precondition simplifies to A.
-- The simplification is left as an exercise (see prose.md).

-- ── 7. Consequence rule ───────────────────────────────────────────────────────

-- If A - A' is PSD (A' ≤ A) and B' - B is PSD (B ≤ B'):
--   {A} c {B} implies {A'} c {B'}
#check @hoare_consequence
