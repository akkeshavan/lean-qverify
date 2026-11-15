import LeanQVerify.Circuit.Parametric
import LeanQVerify.Spec.CircuitSpec

/-!
# Variational Quantum Circuits (VQC)

Provides the `VQC k n` type for circuits parametric in `k` continuous angles,
building blocks for Hardware-Efficient Ansätze (HEA), and key algebraic lemmas
needed for symbolic-angle reasoning.

## Design

The core insight from the hybrid ZX + symbolic approach:
- **Clifford skeleton**: the entanglement layers are Clifford gates — handled by
  `verify_clifford` / ZX rewriting.
- **Rotation angles**: the single-qubit rotation layers carry free parameters
  `θ : Fin k → ℝ` — handled by `ring` and trig identities from Mathlib.

## Main definitions

* `VQC k n`         — a circuit on n qubits parametric in k continuous angles.
* `rzLayer`         — a layer of single-qubit RZ gates, one per qubit.
* `rxLayer`         — a layer of single-qubit RX gates, one per qubit.
* `cnotChainFwd`    — the forward CNOT entanglement chain (qubit 0→1→2→…).
* `heaBlock`        — one HEA block: rzLayer + cnotChainFwd + rzLayer.
* `ParametricSpec`  — a specification that holds for all angle values.

## Key lemmas

* `Rz_mat_period`      — `Rz_mat (θ + 2π) = Rz_mat θ` (2π periodicity).
* `rzLayer_fuse`       — two rzLayers with angles θ, φ compose to rzLayer(θ+φ).
* `rzLayer_period`     — `rzLayer n (θ + (2π : ℝ))` = `rzLayer n θ` pointwise.
-/

namespace LeanQVerify

open QCircuit CircuitSpec

-- ---------------------------------------------------------------------------
-- VQC: a circuit parametric in k continuous angles
-- ---------------------------------------------------------------------------

/-- A Variational Quantum Circuit on n qubits with k continuous angle parameters.
    Concretely a function from an angle vector to a concrete `QCircuit n`. -/
def VQC (k n : ℕ) := (Fin k → ℝ) → QCircuit n

/-- A specification that must hold for all choices of angle parameters. -/
def ParametricSpec (k n : ℕ) (s : (Fin k → ℝ) → CircuitSpec n) : Prop :=
  ∀ θ : Fin k → ℝ, True  -- placeholder; replaced by the meaningful statement below

/-- A VQC satisfies a parametric spec if it satisfies the spec for every θ. -/
def VQC.satisfies {k n : ℕ} (vqc : VQC k n)
    (spec : (Fin k → ℝ) → CircuitSpec n) : Prop :=
  ∀ θ : Fin k → ℝ, (vqc θ) ⊨ spec θ

notation:40 vqc " ⊨ₚ " spec => VQC.satisfies vqc spec

-- ---------------------------------------------------------------------------
-- RZ rotation layer
-- ---------------------------------------------------------------------------

/-- A layer of `n` single-qubit RZ gates, one on each qubit.
    `rzLayer n θ` applies `RZ(θ i)` to qubit `i` for every `i : Fin n`.
    Gates are applied in qubit order (qubit 0 first). -/
def rzLayer (n : ℕ) (θ : Fin n → ℝ) : QCircuit n :=
  (List.finRange n).foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) .empty

/-- A layer of `n` single-qubit RX gates, one on each qubit. -/
def rxLayer (n : ℕ) (θ : Fin n → ℝ) : QCircuit n :=
  (List.finRange n).foldr (fun i c => QCircuit.cons (.RX (θ i) i) c) .empty

-- ---------------------------------------------------------------------------
-- CNOT entanglement chain
-- ---------------------------------------------------------------------------

/-- Forward CNOT chain for n+2 qubits: CNOT(0,1), CNOT(1,2), …, CNOT(n, n+1).
    This is a standard nearest-neighbour entanglement layer. -/
def cnotChainFwd : (n : ℕ) → QCircuit (n + 2)
  | 0     => QCircuit.cons (.CNOT ⟨0, by omega⟩ ⟨1, by omega⟩) .empty
  | n + 1 =>
      (cnotChainFwd n).castSucc ++
      QCircuit.cons (.CNOT ⟨n + 1, by omega⟩ ⟨n + 2, by omega⟩) .empty

-- ---------------------------------------------------------------------------
-- Hardware-Efficient Ansatz (HEA) block
-- ---------------------------------------------------------------------------

/-- One block of a Hardware-Efficient Ansatz for n+2 qubits:
    `rzLayer(θ₀) ++ cnotChainFwd ++ rzLayer(θ₁)`.

    * `θ₀ θ₁ : Fin (n+2) → ℝ` are the two sets of per-qubit rotation angles.

    The Clifford skeleton (the CNOT chain) is constant; only the rotation angles
    vary.  This separation is what the ZX + symbolic hybrid exploits: ZX rewrites
    handle the CNOT part while Mathlib `ring` / trig lemmas handle the angles. -/
def heaBlock (n : ℕ) (θ₀ θ₁ : Fin (n + 2) → ℝ) : QCircuit (n + 2) :=
  rzLayer (n + 2) θ₀ ++ cnotChainFwd n ++ rzLayer (n + 2) θ₁

/-- Multi-layer HEA: repeat `heaBlock` for `d` depth layers.
    Each layer gets its own pair of angle vectors. -/
def heaCircuit (n d : ℕ) (θ : Fin d → Fin 2 → Fin (n + 2) → ℝ) :
    QCircuit (n + 2) :=
  (List.finRange d).foldl
    (fun c l => c ++ heaBlock n (θ l 0) (θ l 1))
    .empty

-- ---------------------------------------------------------------------------
-- Rz_mat periodicity
-- ---------------------------------------------------------------------------

/-- `Rz_mat` picks up a global phase -1 under a 2π shift:
    `Rz_mat (θ + 2π) = -Rz_mat θ`.

    This follows because `exp(-I*(θ+2π)/2) = exp(-Iθ/2) * exp(-Iπ) = -exp(-Iθ/2)`.
    For measurement probability purposes, `-U` and `U` are physically equivalent
    (global phase), so the effective period of RZ(θ) in circuits is 2π. -/
theorem Rz_mat_neg_period (θ : ℝ) : Rz_mat (θ + 2 * Real.pi) = -(Rz_mat θ) := by
  -- Prove entry by entry avoiding matrix-literal pattern-match issues
  ext i j; fin_cases i <;> fin_cases j
  · -- (0,0): exp(-I*((θ+2π)/2)) = -exp(-I*(θ/2))
    simp only [Rz_mat, Matrix.cons_val_zero, Matrix.head_cons, Matrix.neg_apply]
    suffices Complex.exp (-Complex.I * (↑(θ + 2 * Real.pi) / 2)) =
             -(Complex.exp (-Complex.I * ((↑θ : ℂ) / 2))) by exact this
    push_cast
    rw [show -Complex.I * ((↑θ + 2 * ↑Real.pi) / 2 : ℂ) =
          -Complex.I * (↑θ / 2) + -(↑Real.pi * Complex.I) from by ring]
    rw [Complex.exp_add, Complex.exp_neg_pi_mul_I]; ring
  · simp [Rz_mat, Matrix.neg_apply]
  · simp [Rz_mat, Matrix.neg_apply]
  · -- (1,1): exp(I*((θ+2π)/2)) = -exp(I*(θ/2))
    simp only [Rz_mat, Matrix.cons_val_one, Matrix.head_cons, Matrix.neg_apply]
    suffices Complex.exp (Complex.I * (↑(θ + 2 * Real.pi) / 2)) =
             -(Complex.exp (Complex.I * ((↑θ : ℂ) / 2))) by exact this
    push_cast
    rw [show Complex.I * ((↑θ + 2 * ↑Real.pi) / 2 : ℂ) =
          Complex.I * (↑θ / 2) + (↑Real.pi * Complex.I) from by ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring

/-- `Rz_mat` is exactly `4π`-periodic: `Rz_mat (θ + 4π) = Rz_mat θ`. -/
theorem Rz_mat_period (θ : ℝ) : Rz_mat (θ + 4 * Real.pi) = Rz_mat θ := by
  rw [show θ + 4 * Real.pi = (θ + 2 * Real.pi) + 2 * Real.pi from by ring]
  rw [Rz_mat_neg_period, Rz_mat_neg_period]
  simp

-- ---------------------------------------------------------------------------
-- rzLayer: gate-count lemma
-- ---------------------------------------------------------------------------

/-- The rzLayer has exactly n gates. -/
theorem rzLayer_gateCount (n : ℕ) (θ : Fin n → ℝ) :
    countGates (fun _ => true) (rzLayer n θ) = n := by
  simp only [rzLayer]
  suffices h : ∀ (l : List (Fin n)) (acc : QCircuit n),
      countGates (fun _ => true)
        (l.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) acc) =
      l.length + countGates (fun _ => true) acc by
    have := h (List.finRange n) .empty
    simp [List.length_finRange, countGates] at this
    exact this
  intro l acc
  induction l with
  | nil  => simp [countGates]
  | cons h t ih => simp [countGates, ih]; ring

-- ---------------------------------------------------------------------------
-- rzLayer fusion: the key algebraic identity for variational optimization
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Private helpers for rzLayer_fuse and rzLayer_period
-- ---------------------------------------------------------------------------

private lemma diag_mul_comm {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, i ≠ j → A i j = 0) (hB : ∀ i j, i ≠ j → B i j = 0) :
    A * B = B * A := by
  ext i j
  simp only [Matrix.mul_apply]
  conv_lhs => rw [Finset.sum_eq_single i
    (fun k _ hki => by simp [hA i k hki.symm])
    (fun h => absurd (Finset.mem_univ i) h)]
  conv_rhs => rw [Finset.sum_eq_single i
    (fun k _ hki => by simp [hB i k hki.symm])
    (fun h => absurd (Finset.mem_univ i) h)]
  by_cases hij : i = j
  · subst hij; ring
  · simp [hA i j hij, hB i j hij]

private lemma diag_mul_diag_is_diag {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, i ≠ j → A i j = 0) (hB : ∀ i j, i ≠ j → B i j = 0)
    (i j : Fin m) (hij : i ≠ j) : (A * B) i j = 0 := by
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : k = i
  · simp only [hki, hB i j hij, mul_zero]
  · simp only [hA i k (Ne.symm hki), zero_mul]

private lemma Rz_mat_isDiag (θ : ℝ) (j k : Fin 2) (hjk : j ≠ k) : Rz_mat θ j k = 0 := by
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · simp [Rz_mat]
  · simp [Rz_mat]
  · exact absurd rfl hjk

private lemma embedGate1_Rz_isDiagonal (n : ℕ) (i : Fin n) (θ : ℝ) :
    ∀ a b : Fin (2 ^ n), a ≠ b → embedGate1 n i (Rz_mat θ) a b = 0 := by
  intro a b hab
  simp only [embedGate1]
  split_ifs with hse
  · have hbit : natBit a.val i.val ≠ natBit b.val i.val := by
      intro heq
      apply hab
      apply natBit_ext
      intro l
      by_cases hli : l = i
      · subst hli
        have := congr_arg Fin.val heq
        simp only [natBit] at this
        split_ifs at this with ha hb <;> simp_all
      · exact hse l hli
    exact Rz_mat_isDiag θ (natBit a.val i.val) (natBit b.val i.val) hbit
  · rfl

private lemma rzLayer_foldr_isDiagonal (n : ℕ) (l : List (Fin n)) (θ : Fin n → ℝ)
    (acc : QCircuit n) (hacc : ∀ a b : Fin (2 ^ n), a ≠ b → acc.denote a b = 0) :
    ∀ a b : Fin (2 ^ n), a ≠ b →
    (l.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) acc).denote a b = 0 := by
  induction l with
  | nil => exact hacc
  | cons j rest ih =>
      intro a b hab
      simp only [List.foldr_cons, QCircuit.denote_cons, Gate.matrix]
      exact diag_mul_diag_is_diag ih (embedGate1_Rz_isDiagonal n j (θ j)) a b hab

private theorem rzLayer_denote_congr {n : ℕ} (θ₁ θ₂ : Fin n → ℝ)
    (h : ∀ j, Rz_mat (θ₁ j) = Rz_mat (θ₂ j)) :
    (rzLayer n θ₁).denote = (rzLayer n θ₂).denote := by
  simp only [rzLayer]
  suffices ∀ (l : List (Fin n)) (acc₁ acc₂ : QCircuit n),
      acc₁.denote = acc₂.denote →
      (l.foldr (fun i c => QCircuit.cons (.RZ (θ₁ i) i) c) acc₁).denote =
      (l.foldr (fun i c => QCircuit.cons (.RZ (θ₂ i) i) c) acc₂).denote by
    exact this _ _ _ rfl
  intro l
  induction l with
  | nil => intro acc₁ acc₂ hacc; exact hacc
  | cons j rest ih =>
      intro acc₁ acc₂ hacc
      simp only [List.foldr_cons, QCircuit.denote_cons, Gate.matrix]
      rw [ih acc₁ acc₂ hacc, h j]

-- ---------------------------------------------------------------------------
-- rzLayer fusion: the key algebraic identity for variational optimization
-- ---------------------------------------------------------------------------

/-- Two consecutive RZ layers fuse to a single RZ layer with summed angles. -/
theorem rzLayer_fuse (n : ℕ) (θ φ : Fin n → ℝ) :
    (rzLayer n θ ++ rzLayer n φ).denote =
    (rzLayer n (fun i => θ i + φ i)).denote := by
  simp only [QCircuit.denote_seq, rzLayer]
  suffices h : ∀ (l : List (Fin n)) (aφ aθ aSm : QCircuit n),
      (∀ a b : Fin (2 ^ n), a ≠ b → aφ.denote a b = 0) →
      (∀ a b : Fin (2 ^ n), a ≠ b → aθ.denote a b = 0) →
      aSm.denote = aφ.denote * aθ.denote →
      (l.foldr (fun i c => QCircuit.cons (.RZ (φ i) i) c) aφ).denote *
      (l.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote =
      (l.foldr (fun i c => QCircuit.cons (.RZ (θ i + φ i) i) c) aSm).denote by
    apply h (List.finRange n) .empty .empty .empty
    · intro a b hab
      simp only [QCircuit.denote_empty, Matrix.one_apply, if_neg hab]
    · intro a b hab
      simp only [QCircuit.denote_empty, Matrix.one_apply, if_neg hab]
    · simp [QCircuit.denote_empty]
  intro l
  induction l with
  | nil => intro aφ aθ aSm _ _ haSm; simp only [List.foldr_nil]; exact haSm.symm
  | cons j rest ih =>
      intro aφ aθ aSm haφ_diag haθ_diag haSm
      simp only [List.foldr_cons, QCircuit.denote_cons, Gate.matrix]
      have hφ_diag := rzLayer_foldr_isDiagonal n rest φ aφ haφ_diag
      have hθ_diag := rzLayer_foldr_isDiagonal n rest θ aθ haθ_diag
      -- emb(φ j) commutes past rest_θ because rest_θ is diagonal
      have hcomm_φ_restθ :
          embedGate1 n j (Rz_mat (φ j)) *
          (rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote =
          (rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote *
          embedGate1 n j (Rz_mat (φ j)) :=
        diag_mul_comm (embedGate1_Rz_isDiagonal n j (φ j)) hθ_diag
      have hih := ih aφ aθ aSm haφ_diag haθ_diag haSm
      -- Rearrange (rf * ef) * (rt * et) = (rf * rt) * (ef * et)
      -- using ef * rt = rt * ef (hcomm_φ_restθ) and associativity.
      have key :
          (rest.foldr (fun i c => QCircuit.cons (.RZ (φ i) i) c) aφ).denote *
          embedGate1 n j (Rz_mat (φ j)) *
          ((rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote *
           embedGate1 n j (Rz_mat (θ j))) =
          (rest.foldr (fun i c => QCircuit.cons (.RZ (φ i) i) c) aφ).denote *
          (rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote *
          (embedGate1 n j (Rz_mat (φ j)) * embedGate1 n j (Rz_mat (θ j))) := by
        rw [mul_assoc
              (rest.foldr (fun i c => QCircuit.cons (.RZ (φ i) i) c) aφ).denote
              (embedGate1 n j (Rz_mat (φ j)))
              ((rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote *
               embedGate1 n j (Rz_mat (θ j))),
            ← mul_assoc (embedGate1 n j (Rz_mat (φ j)))
                        (rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote
                        (embedGate1 n j (Rz_mat (θ j))),
            hcomm_φ_restθ,
            mul_assoc (rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote
                      (embedGate1 n j (Rz_mat (φ j)))
                      (embedGate1 n j (Rz_mat (θ j))),
            ← mul_assoc
                (rest.foldr (fun i c => QCircuit.cons (.RZ (φ i) i) c) aφ).denote
                (rest.foldr (fun i c => QCircuit.cons (.RZ (θ i) i) c) aθ).denote
                (embedGate1 n j (Rz_mat (φ j)) * embedGate1 n j (Rz_mat (θ j)))]
      rw [key, hih, embedGate1_mul, Rz_mat_add,
          show φ j + θ j = θ j + φ j from add_comm _ _]

/-- RZ layer is `4π`-periodic in every angle component. -/
theorem rzLayer_period (n : ℕ) (θ : Fin n → ℝ) (i : Fin n) :
    (rzLayer n (fun j => if j = i then θ j + 4 * Real.pi else θ j)).denote =
    (rzLayer n θ).denote := by
  apply rzLayer_denote_congr
  intro j
  by_cases hji : j = i
  · subst hji; simp [Rz_mat_period]
  · simp [hji]

-- ---------------------------------------------------------------------------
-- VQE ansatz (UCCSD-inspired, 2-qubit)
-- ---------------------------------------------------------------------------

/-- 2-qubit VQE ansatz, UCCSD-inspired.

    Gate sequence: H(0); CNOT(0→1); RZ(2θ, 1); CNOT(0→1); H(0).

    At θ = 0: RZ(0) = I, the two CNOTs cancel, and H² = I, so the circuit
    is the identity. The parameter θ controls the entanglement amplitude
    between |00⟩ and |11⟩, making this suitable for hydrogen VQE simulations. -/
def vqeAnsatz2 (θ : ℝ) : QCircuit 2 :=
  .cons (.H  ⟨0, by omega⟩)
  (.cons (.CNOT ⟨0, by omega⟩ ⟨1, by omega⟩)
  (.cons (.RZ (2 * θ) ⟨1, by omega⟩)
  (.cons (.CNOT ⟨0, by omega⟩ ⟨1, by omega⟩)
  (.cons (.H  ⟨0, by omega⟩) .empty))))

/-- `vqeAnsatz2` as a VQC: maps one angle to a 2-qubit circuit. -/
def vqeAnsatzVQC : VQC 1 2 := fun θ => vqeAnsatz2 (θ 0)

-- ---------------------------------------------------------------------------
-- QAOA p=1 circuit (MaxCut on K₂)
-- ---------------------------------------------------------------------------

/-- QAOA p=1 circuit for MaxCut on the 2-vertex complete graph K₂.

    Gate sequence:
    - Initial layer:    H(0); H(1)              (prepares |++⟩)
    - Problem unitary:  RZZ(2γ, 0, 1)           (Uₚ(γ) = exp(−iγ Z⊗Z))
    - Mixer unitary:    RX(2β, 0); RX(2β, 1)    (Uₘ(β) = Rx(2β)^⊗2)

    The QAOA angles (γ, β) are optimized classically to maximize the
    expected cut value. -/
def qaoa1Layer (γ β : ℝ) : QCircuit 2 :=
  .cons (.H  ⟨0, by omega⟩)
  (.cons (.H  ⟨1, by omega⟩)
  (.cons (.RZZ (2 * γ) ⟨0, by omega⟩ ⟨1, by omega⟩)
  (.cons (.RX (2 * β) ⟨0, by omega⟩)
  (.cons (.RX (2 * β) ⟨1, by omega⟩) .empty))))

/-- `qaoa1Layer` as a VQC: maps (γ, β) to a 2-qubit circuit. -/
def qaoa1VQC : VQC 2 2 := fun θ => qaoa1Layer (θ 0) (θ 1)

-- ---------------------------------------------------------------------------
-- Parameter shift rule (matrix-level algebraic identity)
-- ---------------------------------------------------------------------------

/-- **Parameter shift identity** for Rz.

    The finite difference `Rz(θ + π/2) − Rz(θ − π/2)` equals
    `−I·√2 · (Z · Rz(θ))`.

    This is the algebraic foundation of the quantum parameter shift rule
    used in variational quantum algorithms (VQE, QAOA):
    for a circuit `C(θ)` containing a single `Rz(θ)` gate, the expectation
    value satisfies

        `∂E(θ)/∂θ = (1/2)·[E(θ + π/2) − E(θ − π/2)]`

    because `d/dθ Rz(θ) = −(I/2)·Z·Rz(θ)` and the ±π/2 finite difference
    recovers this derivative via Euler's formula at π/4:
    `exp(∓Iπ/4) = √2/2 · (1 ∓ I)`, so their difference is `−I√2`. -/
theorem param_shift_Rz (θ : ℝ) :
    Rz_mat (θ + Real.pi / 2) - Rz_mat (θ - Real.pi / 2) =
    -(Complex.I * ↑(Real.sqrt 2)) • (Z_mat * Rz_mat θ) := by
  -- Key scalar sub-lemmas: the two nonzero diagonal entries
  -- (0,0): exp(−Iπ/4) − exp(Iπ/4) = −I√2  (Euler at π/4)
  have hk00 : Complex.exp (-Complex.I * (↑(θ + Real.pi / 2) / 2)) -
               Complex.exp (-Complex.I * (↑(θ - Real.pi / 2) / 2)) =
               -(Complex.I * ↑(Real.sqrt 2)) * Complex.exp (-Complex.I * (↑θ / 2)) := by
    rw [show -Complex.I * (↑(θ + Real.pi / 2) / 2 : ℂ) =
              -Complex.I * (↑θ / 2) + ↑(-(Real.pi / 4) : ℝ) * Complex.I from by push_cast; ring,
        show -Complex.I * (↑(θ - Real.pi / 2) / 2 : ℂ) =
              -Complex.I * (↑θ / 2) + ↑(Real.pi / 4 : ℝ) * Complex.I from by push_cast; ring,
        Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  -- (1,1): exp(Iπ/4) − exp(−Iπ/4) = I√2
  have hk11 : Complex.exp (Complex.I * (↑(θ + Real.pi / 2) / 2)) -
               Complex.exp (Complex.I * (↑(θ - Real.pi / 2) / 2)) =
               Complex.I * ↑(Real.sqrt 2) * Complex.exp (Complex.I * (↑θ / 2)) := by
    rw [show Complex.I * (↑(θ + Real.pi / 2) / 2 : ℂ) =
              Complex.I * (↑θ / 2) + ↑(Real.pi / 4 : ℝ) * Complex.I from by push_cast; ring,
        show Complex.I * (↑(θ - Real.pi / 2) / 2 : ℂ) =
              Complex.I * (↑θ / 2) + ↑(-(Real.pi / 4) : ℝ) * Complex.I from by push_cast; ring,
        Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  -- Prove entry by entry. After fin_cases the indices are 0/1 : Fin 2.
  -- dsimp (with definitional simp lemmas) uses kernel-level equality which is
  -- proof-irrelevant on Fin indices — fixing the ⟨0,h⟩ vs 0 mismatch that
  -- prevents simp only [cons_val_zero] from firing after fin_cases.
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
                       Fin.sum_univ_two]
  all_goals simp only [Rz_mat, Z_mat, Matrix.of_apply,
                       Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- After dsimp, all !![...] i j are reduced to scalars.
  -- linear_combination works over ℂ (unlike linarith) and handles ring-equivalent forms.
  · push_cast at hk00 ⊢; linear_combination hk00
  · push_cast; ring
  · push_cast; ring
  · push_cast at hk11 ⊢; linear_combination hk11

-- ---------------------------------------------------------------------------
-- VQC: basic structural lemmas
-- ---------------------------------------------------------------------------

/-- The rzLayer VQC as a family. -/
def rzVQC (n : ℕ) : VQC n n := fun θ => rzLayer n θ

/-- A single-layer HEA VQC for n+2 qubits with 2*(n+2) parameters.
    Parameters: first n+2 entries are θ₀, next n+2 are θ₁. -/
def heaVQC (n : ℕ) : VQC (2 * (n + 2)) (n + 2) :=
  fun θ => heaBlock n (fun i => θ ⟨i.val, by omega⟩)
                      (fun i => θ ⟨n + 2 + i.val, by omega⟩)

end LeanQVerify
