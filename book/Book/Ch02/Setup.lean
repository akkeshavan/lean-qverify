import LeanQVerify.Foundation.QState
import LeanQVerify.Circuit.Gate
import LeanQVerify.Circuit.QCircuit
import LeanQVerify.Circuit.Parametric
import LeanQVerify.Spec.StandardSpecs

/-!
# Chapter 2 — Setup

If this file compiles without errors, your environment is working correctly.

Run from inside the book/ directory:
  lake build Book.Ch02.Setup
-/

open LeanQVerify

-- Core types
#check QState    -- n-qubit pure quantum state
#check Gate      -- quantum gate for an n-qubit system
#check QCircuit  -- a sequence of gates

-- The satisfaction relation
#check @CircuitSpec.satisfies  -- circuit ⊨ spec

-- Confirmed: the library is accessible
#check @bellPrep_twoGates
#check @groverStep2_correct
#check @ghzCircuit_gateCount
