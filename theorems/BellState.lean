/-!
# Bell State Theorems (T1–T5)

Paper section: §5, Table 1, rows T1–T5.

Every `example` below is a type-checked alias of the named theorem.
Lean's kernel must verify the type matches the stated proposition.
A clean `lake build` with no `sorry` in the proof tree is the guarantee.
-/

import LeanQVerify.Spec.StandardSpecs

open LeanQVerify QCircuit CircuitSpec

-- T1: Bell preparation circuit uses exactly 2 gates.
example : bellPrep ⊨ totalGates 2 :=
  bellPrep_twoGates

-- T2: Bell preparation circuit contains exactly 1 CNOT gate.
example : bellPrep ⊨ maxCNOTs 1 :=
  bellPrep_oneCNOT

-- T3: Bell preparation circuit has parallel depth ≤ 2.
example : bellPrep ⊨ .maxDepth 2 :=
  bellPrep_depth

-- T4: Measuring qubit 0 of the Bell state starting from |00⟩ gives outcome 0
--     with probability ≥ 1/2.
example : bellPrep ⊨ .measurementProb QState.ket00 0 false (1/2) :=
  bellPrep_entangled

-- T5: Measuring qubit 0 of the Bell state starting from |00⟩ gives outcome 1
--     with probability ≥ 1/2.
example : bellPrep ⊨ .measurementProb QState.ket00 0 true (1/2) :=
  bellPrep_entangled_one
