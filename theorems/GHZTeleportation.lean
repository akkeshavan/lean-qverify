/-!
# GHZ and Teleportation Theorems (T6–T8)

Paper section: §5, Table 1, rows T6–T8.

Note on T8: the teleportation theorem covers only the pre-measurement unitary
portion of the protocol.  The classical correction step requires a model of
classical wires not yet present in the library (see Open Problems, §7).
-/

import LeanQVerify.Spec.StandardSpecs

open LeanQVerify QCircuit CircuitSpec

-- T6: GHZ preparation circuit uses exactly 3 gates.
example : ghzPrep ⊨ .gateCount (fun _ => true) 3 :=
  ghzPrep_threeGates

-- T7: GHZ preparation circuit has parallel depth ≤ 3.
example : ghzPrep ⊨ .maxDepth 3 :=
  ghzPrep_depth

-- T8: Teleportation circuit (pre-measurement unitary) has parallel depth ≤ 4.
example : teleportPrep ⊨ .maxDepth 4 :=
  teleportPrep_depth
