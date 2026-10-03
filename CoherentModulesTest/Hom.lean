/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

public import CoherentModules.Hom
public import Mathlib.Data.ZMod.Basic

/-!
External-use checks for coherence of linear-map modules.
-/

namespace CoherentModulesTest.Hom

universe u v w

private theorem linearMapCoherent (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M →ₗ[R] N) :=
  Module.IsCoherent.linearMap

/-- The rank-zero presentation gives the empty-product boundary case. -/
private theorem rankZeroLinearMap (R : Type u) [CommRing R]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.IsCoherent R N] :
    Module.IsCoherent R ((Fin 0 → R) →ₗ[R] N) :=
  Module.IsCoherent.linearMap

/-- The API remains valid over the zero ring, with source and target in independent universes. -/
public theorem zeroRingIndependentUniverses :
    Module.IsCoherent (ZMod 1) (PUnit.{1} →ₗ[ZMod 1] PUnit.{2}) :=
  Module.IsCoherent.linearMap

-- Selected named-client axiom checks, not a complete release census.
#print axioms linearMapCoherent
#print axioms rankZeroLinearMap
#print axioms zeroRingIndependentUniverses

end CoherentModulesTest.Hom
