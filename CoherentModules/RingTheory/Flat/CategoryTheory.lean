/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Flat modules and finite-limit preservation in semimodules

Over a commutative ring, tensoring with a flat semimodule preserves finite
limits. The comparison uses the existing equivalence between `ModuleCat` and
`SemimoduleCat`, including its monoidal structure, and retains the given
semimodule action.

## References

This extends the categorical formulation of flatness in Mathlib, formalized by
Jujian Zhang, along Mathlib's module–semimodule equivalence and its monoidal
transport interfaces.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

/-- Over a commutative ring, left tensoring with a flat semimodule preserves
finite limits in the category of semimodules. -/
theorem Module.Flat.preservesFiniteLimits_tensorLeft_semimoduleCat
    {R : Type u} [CommRing R] (M : SemimoduleCat.{u} R) [Module.Flat R M] :
    PreservesFiniteLimits (tensorLeft M) := by
  let E : ModuleCat.{u} R ≌ SemimoduleCat.{u} R :=
    ModuleCat.equivalenceSemimoduleCat
  let B := E.inverse.obj M
  let counitLinearEquiv : E.functor.obj B ≃ₗ[R] M :=
    (E.counitIso.app M).toLinearEquivₛ
  have : Module.Flat R B := Module.Flat.of_linearEquiv counitLinearEquiv
  let : E.functor.Monoidal := by
    dsimp only [E]
    unfold ModuleCat.monoidalCategory
    infer_instance
  let : E.inverse.Monoidal := E.inverseMonoidal
  have : PreservesFiniteLimits (E.inverse ⋙ tensorLeft B) := inferInstance
  have : PreservesFiniteLimits (tensorLeft M ⋙ E.inverse) :=
    preservesFiniteLimits_of_natIso (Functor.Monoidal.commTensorLeft E.inverse M)
  exact preservesFiniteLimits_of_reflects_of_preserves (tensorLeft M) E.inverse
