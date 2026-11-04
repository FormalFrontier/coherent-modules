/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.ULift

/-!
# Semilinear equivalence for universe lifts

`ULift.semilinearModuleEquiv` simultaneously unlifts a coefficient semiring
and a module carrier. The two lift levels are independent, and both lifted
actions come from the given module action.

Its underlying additive equivalence agrees with that of Mathlib's
`ULift.moduleEquiv`, which unlifts the carrier while keeping the coefficient
semiring fixed. The forward and inverse application and scalar-action laws
characterize the comparison.

## Implementation notes

The inverse coefficient homomorphism is the inverse of `ULift.ringEquiv`.
The corresponding `RingHomInvPair` lemmas are used only as local instances.
-/

@[expose] public section

universe uA uM vA vM

namespace ULift

variable (A : Type uA) (M : Type uM) [Semiring A] [AddCommMonoid M] [Module A M]

local instance ringEquiv_invPair : RingHomInvPair
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (ULift.ringEquiv : ULift.{vA} A ≃+* A)

local instance ringEquiv_invPair_symm : RingHomInvPair
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).symm.toRingHom
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (ULift.ringEquiv : ULift.{vA} A ≃+* A)

/-- Simultaneously unlift a coefficient semiring and a module carrier.
The coefficient and carrier lift levels are independent. The underlying
additive equivalence is that of `ULift.moduleEquiv`. -/
def semilinearModuleEquiv :
    ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M where
  __ := (ULift.moduleEquiv : ULift.{vM} M ≃ₗ[A] M).toAddEquiv
  map_smul' _ _ := rfl

/-- The underlying additive equivalence agrees with the one obtained by
unlifting only the carrier and retaining the coefficient semiring. -/
theorem semilinearModuleEquiv_toAddEquiv :
    (semilinearModuleEquiv A M :
      ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M).toAddEquiv =
        (ULift.moduleEquiv : ULift.{vM} M ≃ₗ[A] M).toAddEquiv := rfl

/-- The lifted-module comparison unpacks the given element. -/
@[simp]
theorem semilinearModuleEquiv_apply (x : ULift.{vM} M) :
    (semilinearModuleEquiv A M :
      ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M) x = x.down := rfl

/-- The inverse comparison is the lift constructor. -/
@[simp]
theorem semilinearModuleEquiv_symm_apply (x : M) :
    (semilinearModuleEquiv A M :
      ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M).symm x =
        ULift.up x := rfl

/-- The comparison retains the given scalar multiplication. -/
theorem semilinearModuleEquiv_smul (r : ULift.{vA} A) (x : ULift.{vM} M) :
    (semilinearModuleEquiv A M :
      ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M) (r • x) =
      r.down • (semilinearModuleEquiv A M :
        ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M) x := rfl

/-- The inverse comparison also retains the given scalar multiplication. -/
theorem semilinearModuleEquiv_symm_smul (r : A) (x : M) :
    (semilinearModuleEquiv A M :
      ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M).symm (r • x) =
      (ULift.up r : ULift.{vA} A) • (semilinearModuleEquiv A M :
        ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M).symm x := rfl

end ULift
