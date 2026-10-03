/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

public import CoherentModules
public import Mathlib.Data.ZMod.Basic

/-!
Zero-universe and subsingleton checks for the finite-presentation/coherence
bridge.
-/

namespace CoherentModulesTest.FinitePresentationZero

private theorem zeroRingCoherentUnit : Module.IsCoherent (ZMod 1) PUnit :=
  Module.FinitePresentation.isCoherent

private theorem zeroRingRankZeroCriterion :
    Module.IsCoherent (ZMod 1) (Fin 0 → ZMod 1) ↔
      Module.FinitePresentation (ZMod 1) (Fin 0 → ZMod 1) :=
  Module.isCoherent_iff_finitePresentation

private theorem zeroRingKernel : Module.FinitePresentation (ZMod 1)
    (LinearMap.ker
      (0 : (Fin 0 → ZMod 1) →ₗ[ZMod 1] (Fin 0 → ZMod 1))) :=
  Module.FinitePresentation.ker 0

/-- The exact-five criterion applies even when all five modules are over the zero ring. -/
public theorem zeroRingExactFive : Module.FinitePresentation (ZMod 1) PUnit.{1} := by
  apply Module.FinitePresentation.of_exact_five
      (0 : PUnit.{1} →ₗ[ZMod 1] PUnit.{1}) (0 : PUnit.{1} →ₗ[ZMod 1] PUnit.{1})
      (0 : PUnit.{1} →ₗ[ZMod 1] PUnit.{1}) (0 : PUnit.{1} →ₗ[ZMod 1] PUnit.{1})
  all_goals intro x
  all_goals simp

-- Selected named-client axiom checks, not a complete release census.
#print axioms zeroRingCoherentUnit
#print axioms zeroRingRankZeroCriterion
#print axioms zeroRingKernel
#print axioms zeroRingExactFive

end CoherentModulesTest.FinitePresentationZero
