/-!
# Grover's Algorithm Theorem (T25)

Paper section: §5, Table 1, row T25.

Circuit: 2-qubit Grover search, 1 iteration, target state |11⟩.
The full circuit is: H⊗H (initial superposition) → CZ oracle → diffusion operator.

The theorem states that measuring qubit 0 after one Grover step gives outcome 1
with probability ≥ 0.99.  The actual probability is exactly 1 (the 2-qubit,
1-iteration case is perfect), so the ≥ 0.99 bound is strict.

The proof proceeds by computing the explicit 4×4 unitary, applying it to |00⟩,
and evaluating the measurement probability sum with `norm_num`.
-/

import LeanQVerify.Spec.StandardSpecs

open LeanQVerify QCircuit CircuitSpec

-- T25: One Grover step on 2 qubits finds the marked state |11⟩ with
--      probability ≥ 0.99 (exact probability is 1).
example :
    (QCircuit.ofGate (.H 0) ++ QCircuit.ofGate (.H 1) ++ groverStep2)
    ⊨ .measurementProb QState.ket00 0 true 0.99 :=
  groverStep2_correct
