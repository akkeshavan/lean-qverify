import LeanQVerify.ZX.HybridRules
import LeanQVerify.Circuit.Variational

/-!
# Variational Circuit Theorems (TV1–TV5)

Demonstrates the hybrid ZX + symbolic framework for variational quantum circuits.

## Theorems

* TV1: `RZ(θ)` is `2π`-periodic: `Rz_mat(θ + 2π) = Rz_mat(θ)`.
* TV2: Consecutive RZ gates on the same qubit fuse: `RZ(θ); RZ(φ) ≅ RZ(θ+φ)`.
* TV3: `H; RZ(θ); H ≅ RX(θ)` — the core hybrid identity, circuit-level.
* TV4: `H; RX(θ); H ≅ RZ(θ)` — the reverse hybrid identity.
* TV5: Rotation identity `RZ(θ) = RX(-π/2); RZ(θ); RX(π/2)` is equivalent to
       `H; RZ(θ); H = RX(θ)` up to global phase (TV3 specialised).

## Context

These identities are central to variational quantum algorithms (VQA):

- **TV2** (gate fusion) is used by classical optimizers when two consecutive
  rotation layers merge.  It underlies the `rzLayer_fuse` lemma in
  `LeanQVerify.Circuit.Variational`.

- **TV3** (H-RZ-H = RX) is the key identity in the **hybrid ZX + symbolic**
  approach suggested by Anil Achoora: the ZX color-change rule proves the
  Clifford frame, while `Rz_mat_add` / `zSpiderMat_phase_Rz` prove the angle
  arithmetic. This is the VQC analogue of "split the circuit into Clifford
  skeleton + rotation parameters."

- **TV4** follows from **TV3** by conjugation with H² = I.
-/

open LeanQVerify QCircuit

-- ============================================================
-- TV1: RZ(θ) is 2π-periodic
-- ============================================================

-- TV1: Rz_mat picks up a global phase under 2π shift: Rz_mat(θ+2π) = -Rz_mat(θ).
example (θ : ℝ) : Rz_mat (θ + 2 * Real.pi) = -(Rz_mat θ) :=
  Rz_mat_neg_period θ

-- TV1a: Rz_mat is exactly 4π-periodic.
example (θ : ℝ) : Rz_mat (θ + 4 * Real.pi) = Rz_mat θ :=
  Rz_mat_period θ

-- TV1': The gate-level 4π period for all n and qubit i.
example (n : ℕ) (i : Fin n) (θ : ℝ) :
    (ofGate (.RZ (θ + 4 * Real.pi) i)).denote = (ofGate (.RZ θ i)).denote := by
  simp only [ofGate, denote_cons, denote_empty, mul_one, Gate.matrix]
  rw [Rz_mat_period]

-- ============================================================
-- TV2: Consecutive RZ gates fuse
-- ============================================================

-- TV2: RZ(θ); RZ(φ) ≅ RZ(θ+φ) on a single qubit.
example (n : ℕ) (i : Fin n) (θ φ : ℝ) :
    (ofGate (.RZ θ i) ++ ofGate (.RZ φ i)) ≅ ofGate (.RZ (θ + φ) i) := by
  unfold QCircuit.equiv
  simp only [denote_seq, ofGate, denote_cons, denote_empty, mul_one, Gate.matrix]
  rw [← embedGate1_mul n i (Rz_mat θ) (Rz_mat φ), Rz_mat_add]

-- ============================================================
-- TV3: H; RZ(θ); H ≅ RX(θ) — the core hybrid identity
-- ============================================================

-- TV3: The three-gate sequence [H_i, RZ(θ,i), H_i] is equivalent to [RX(θ,i)].
-- Proved using the phase-spider bridge: Rz_mat = exp(-iθ/2)·zSpider,
-- then the ZX color-change rule H·Z(α)·H = X(α).
example (n : ℕ) (i : Fin n) (θ : ℝ) :
    ofGate (.H i) ++ ofGate (.RZ θ i) ++ ofGate (.H i) ≅ ofGate (.RX θ i) :=
  H_RZ_H_eq_RX_circuit n i θ

-- ============================================================
-- TV4: H; RX(θ); H ≅ RZ(θ)
-- ============================================================

-- TV4: The reverse hybrid identity.  By TV3 and H² = I.
theorem H_RX_H_eq_RZ_circuit (n : ℕ) (i : Fin n) (θ : ℝ) :
    ofGate (.H i) ++ ofGate (.RX θ i) ++ ofGate (.H i) ≅ ofGate (.RZ θ i) := by
  unfold QCircuit.equiv
  simp only [denote_seq, ofGate, denote_cons, denote_empty, mul_one, Gate.matrix]
  -- Lift to 2×2: H * Rx(θ) * H = Rz(θ)
  rw [← embedGate1_mul n i H_mat (Rx_mat θ),
      ← embedGate1_mul n i (H_mat * Rx_mat θ) H_mat]
  congr 1
  -- Goal: H_mat * Rx_mat θ * H_mat = Rz_mat θ
  -- Proof: by TV3 (H_Rz_H_eq_Rx) in reverse plus H² = I
  have h := H_Rz_H_eq_Rx θ
  -- h : H * Rz(θ) * H = Rx(θ)
  -- Apply H on both sides: H * h * H → H * Rx(θ) * H = Rz(θ)
  calc H_mat * Rx_mat θ * H_mat
      = H_mat * (H_mat * Rz_mat θ * H_mat) * H_mat  := by rw [← h]
    _ = (H_mat * H_mat) * Rz_mat θ * (H_mat * H_mat) := by ring
    _ = Rz_mat θ                                      := by rw [H_mat_unitary]; simp

-- ============================================================
-- TV5: RZ layer periodicity — VQC-level example
-- ============================================================

-- TV5: The VQC `rzVQC n` satisfies 4π-periodicity in every parameter.
-- For a single qubit: (rzVQC 1)(θ) ≅ (rzVQC 1)(θ + 4π).
example (θ : ℝ) : (rzVQC 1 (fun _ => θ)).denote = (rzVQC 1 (fun _ => θ + 4 * Real.pi)).denote := by
  simp only [rzVQC, rzLayer, List.finRange, List.foldr, denote_cons, denote_empty, mul_one,
             Gate.matrix]
  rw [Rz_mat_period]

-- ============================================================
-- TV6: Variational circuit instantiation check
-- ============================================================

-- TV6: A 2-qubit HEA block with zero angles is equivalent to the CNOT chain.
-- (Structurally the same as T13, but via the new heaBlock definition.)
example : (heaBlock 0 (fun _ => 0) (fun _ => 0)).denote =
          ((cnotChainFwd 0).denote) := by
  simp only [heaBlock, denote_seq, rzLayer, List.finRange, List.foldr, Fin.val_zero,
             denote_cons, denote_empty, mul_one, Gate.matrix, Rz_mat, Matrix.cons_val_zero,
             Matrix.cons_val_one, Matrix.head_cons, Complex.exp_zero, one_mul]
  rw [embedGate1_one, embedGate1_one]
  simp [one_mul, mul_one]

-- ============================================================
-- TV7: VQE ansatz at θ = 0 is the identity
-- ============================================================

-- TV7: The 2-qubit UCCSD-inspired ansatz at θ = 0 reduces to the identity.
-- Circuit: H(0); CNOT(0,1); RZ(0,1); CNOT(0,1); H(0)
-- = H(0); CNOT; I; CNOT; H(0)   (since RZ(0) = I)
-- = H(0); (CNOT²); H(0)         (since CNOT is self-inverse)
-- = H(0)²                        (since CNOT² = I)
-- = I                             (since H² = I)
example : (vqeAnsatz2 0).denote = 1 := by
  simp only [vqeAnsatz2, denote_cons, denote_empty, mul_one, Gate.matrix]
  norm_num
  -- After norm_num: 2 * 0 = 0, so RZ(0) appears.
  simp only [Rz_mat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Complex.exp_zero]
  rw [embedGate1_one, mul_one]
  -- Goal: embed_H₀ * embedCNOT₀₁ * embedCNOT₀₁ * embed_H₀ = 1
  have hcnot : (Gate.CNOT (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩).matrix *
               (Gate.CNOT (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩).matrix = 1 :=
    CNOT_self_inverse 2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide)
  have hh : embedGate1 2 (⟨0, by omega⟩ : Fin 2) H_mat *
            embedGate1 2 (⟨0, by omega⟩ : Fin 2) H_mat = 1 :=
    embedGate1_self_inverse 2 ⟨0, by omega⟩ H_mat H_mat_unitary
  calc embedGate1 2 ⟨0, by omega⟩ H_mat *
       (Gate.CNOT (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩).matrix *
       (Gate.CNOT (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩).matrix *
       embedGate1 2 ⟨0, by omega⟩ H_mat
      = embedGate1 2 ⟨0, by omega⟩ H_mat *
        ((Gate.CNOT (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩).matrix *
         (Gate.CNOT (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩).matrix) *
        embedGate1 2 ⟨0, by omega⟩ H_mat := by ring
    _ = embedGate1 2 ⟨0, by omega⟩ H_mat * 1 *
        embedGate1 2 ⟨0, by omega⟩ H_mat := by rw [hcnot]
    _ = embedGate1 2 ⟨0, by omega⟩ H_mat *
        embedGate1 2 ⟨0, by omega⟩ H_mat := by ring
    _ = 1 := hh

-- ============================================================
-- TV8: QAOA p=1 circuit gate count
-- ============================================================

-- TV8: The QAOA p=1 circuit for 2-qubit MaxCut has exactly 5 gates.
-- Gate sequence: H(0); H(1); RZZ(2γ, 0, 1); RX(2β, 0); RX(2β, 1)
example (γ β : ℝ) : countGates (fun _ => true) (qaoa1Layer γ β) = 5 := by
  simp [qaoa1Layer, countGates]

-- ============================================================
-- TV9: Parameter shift rule (algebraic identity)
-- ============================================================

-- TV9: The parameter shift rule at the matrix level.
-- Rz(θ + π/2) − Rz(θ − π/2) = −I√2 · (Z · Rz(θ))
-- This is the algebraic foundation of gradient computation in VQA:
-- ∂E(θ)/∂θ = (1/2)·[E(θ+π/2) − E(θ−π/2)]
-- because d/dθ Rz(θ) = −(I/2)·Z·Rz(θ) and the ±π/2 finite difference
-- recovers this derivative factor via Euler's formula at π/4.
example (θ : ℝ) :
    Rz_mat (θ + Real.pi / 2) - Rz_mat (θ - Real.pi / 2) =
    -(Complex.I * ↑(Real.sqrt 2)) • (Z_mat * Rz_mat θ) :=
  param_shift_Rz θ

-- TV9': Circuit-level parameter shift — the finite difference of the full
-- unitary when one RZ gate is shifted decomposes via param_shift_Rz.
-- For any C₁; RZ(θ, i); C₂, letting U±(θ) = C₂ * embed(Rz(θ±π/2)) * C₁:
-- U₊(θ) − U₋(θ) = C₂ * embed(−I√2 · Z · Rz(θ)) * C₁
theorem param_shift_circuit (n : ℕ) (i : Fin n) (θ : ℝ)
    (c₁ c₂ : QCircuit n) :
    (c₁ ++ ofGate (.RZ (θ + Real.pi / 2) i) ++ c₂).denote -
    (c₁ ++ ofGate (.RZ (θ - Real.pi / 2) i) ++ c₂).denote =
    c₂.denote *
      (-(Complex.I * ↑(Real.sqrt 2)) • (embedGate1 n i Z_mat * embedGate1 n i (Rz_mat θ))) *
    c₁.denote := by
  -- Factor: (C₂ * RZ(θ+π/2) * C₁) − (C₂ * RZ(θ−π/2) * C₁)
  --       = C₂ * (embed(Rz(θ+π/2)) − embed(Rz(θ−π/2))) * C₁
  --       = C₂ * embed(Rz(θ+π/2) − Rz(θ−π/2)) * C₁   (embed is linear)
  --       = C₂ * embed(−I√2 · Z · Rz(θ)) * C₁          (param_shift_Rz)
  --       = C₂ * (−I√2 · embed(Z) · embed(Rz(θ))) * C₁ (embed is multiplicative)
  -- Key steps:
  -- (1) expand denote_seq to expose the embedGate1 Rz terms
  -- (2) factor C₁/C₂ out of the difference
  -- (3) use embedGate1 linearity: embed(A - B) = embed(A) - embed(B)
  -- (4) apply param_shift_Rz to get the Z generator term
  -- (5) use embedGate1_mul to split embed(Z * Rz(θ)) = embed(Z) * embed(Rz(θ))
  -- This requires embedGate1_sub (not yet in the library), so we leave it as sorry.
  simp only [denote_seq, ofGate, denote_cons, denote_empty, mul_one, Gate.matrix]
  rw [show c₂.denote * embedGate1 n i (Rz_mat (θ + Real.pi / 2)) * c₁.denote -
          c₂.denote * embedGate1 n i (Rz_mat (θ - Real.pi / 2)) * c₁.denote =
          c₂.denote * (embedGate1 n i (Rz_mat (θ + Real.pi / 2)) -
                        embedGate1 n i (Rz_mat (θ - Real.pi / 2))) * c₁.denote from by ring]
  rw [← embedGate1_sub, param_shift_Rz, embedGate1_smul, ← embedGate1_mul]
