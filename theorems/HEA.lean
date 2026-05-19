/-!
# Hardware-Efficient Ansatz Theorems (T9–T14)

Paper section: §5, Table 1, rows T9–T14.

`hea4 θ₀ θ₁ θ₂ θ₃` is one layer of a 4-qubit hardware-efficient ansatz:
  RZ(θ₀) on qubit 0, RZ(θ₁) on qubit 1, RZ(θ₂) on qubit 2, RZ(θ₃) on qubit 3,
  followed by a linear CNOT entangling chain CNOT(0,1), CNOT(1,2), CNOT(2,3).

Note on the negative result: full two-layer parameter fusion
  hea4(θ) ++ hea4(φ) ≅ hea4(θ+φ)
does NOT hold because the CNOT chain does not commute with RZ on target qubits.
This is confirmed and discussed in the paper (§5).  Only single-qubit RZ fusion
(T14) holds.
-/

import LeanQVerify.Spec.StandardSpecs

open LeanQVerify QCircuit CircuitSpec

-- T9: HEA layer uses exactly 7 gates in total.
example (θ₀ θ₁ θ₂ θ₃ : ℝ) : hea4 θ₀ θ₁ θ₂ θ₃ ⊨ .gateCount (fun _ => true) 7 :=
  hea4_gateCount θ₀ θ₁ θ₂ θ₃

-- T10: HEA layer contains exactly 3 CNOT gates.
example (θ₀ θ₁ θ₂ θ₃ : ℝ) :
    hea4 θ₀ θ₁ θ₂ θ₃ ⊨
      .gateCount (fun g => match g with | .CNOT .. => true | _ => false) 3 :=
  hea4_cnotCount θ₀ θ₁ θ₂ θ₃

-- T11: HEA layer contains exactly 4 RZ gates.
example (θ₀ θ₁ θ₂ θ₃ : ℝ) :
    hea4 θ₀ θ₁ θ₂ θ₃ ⊨
      .gateCount (fun g => match g with | .RZ .. => true | _ => false) 4 :=
  hea4_rzCount θ₀ θ₁ θ₂ θ₃

-- T12: HEA layer has parallel depth ≤ 4.
example (θ₀ θ₁ θ₂ θ₃ : ℝ) : hea4 θ₀ θ₁ θ₂ θ₃ ⊨ .maxDepth 4 :=
  hea4_depth θ₀ θ₁ θ₂ θ₃

-- T13: Setting all rotation angles to 0 collapses hea4 to the bare CNOT chain.
--      (RZ(0) = I, so the rotation layer vanishes.)
example : hea4 0 0 0 0 ≅ cnotChain4 :=
  hea4_zero_eq_cnotChain

-- T14: Two consecutive RZ rotations on the same qubit fuse by angle addition.
--      This is the identity underlying parameter-shift and angle compilation.
example (i : Fin 4) (θ φ : ℝ) :
    (QCircuit.ofGate (.RZ θ i) ++ QCircuit.ofGate (.RZ φ i))
    ≅ QCircuit.ofGate (.RZ (θ + φ) i) :=
  hea4_rz_fuse_single i θ φ
