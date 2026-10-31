/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Flat.Equiv
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.Prod

/-!
# A coefficient swap between projection modules

The first-projection module over `ℕ × ℕ` is flat as a retract of the regular
module. Swapping the two coefficients and lifting gives flatness of the
second-projection module over `ULift (ℕ × ℕ)`. Both given actions are nonfaithful;
without the coefficient swap, the displayed additive equivalence is not linear.
The coefficient and module lift levels are independent.

The fixed-ring check passes the same ordinary linear equivalence to both
semilinear flatness declarations, without rebundling it or changing an action.

## References

The examples use Mathlib's regular-module flatness, `Module.Flat.of_retract`,
product projections, product-swap ring equivalence and lift equivalences.
-/

universe vS vN uR uM uN

example :
    @Module.Flat (ULift.{vS} (ℕ × ℕ)) (ULift.{vN} ℕ)
      inferInstance inferInstance
      (Module.compHom (ULift.{vN} ℕ)
        ((RingHom.snd ℕ ℕ).comp
          (ULift.ringEquiv : ULift.{vS} (ℕ × ℕ) ≃+* (ℕ × ℕ)).toRingHom)) := by
  let moduleM : Module (ℕ × ℕ) ℕ := Module.compHom ℕ (RingHom.fst ℕ ℕ)
  let moduleN : Module (ULift.{vS} (ℕ × ℕ)) (ULift.{vN} ℕ) :=
    Module.compHom (ULift.{vN} ℕ)
      ((RingHom.snd ℕ ℕ).comp
        (ULift.ringEquiv : ULift.{vS} (ℕ × ℕ) ≃+* (ℕ × ℕ)).toRingHom)
  let e : (ℕ × ℕ) ≃+* ULift.{vS} (ℕ × ℕ) :=
    (RingEquiv.prodComm : (ℕ × ℕ) ≃+* (ℕ × ℕ)).trans
      (ULift.ringEquiv : ULift.{vS} (ℕ × ℕ) ≃+* (ℕ × ℕ)).symm
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let E : @LinearEquiv (ℕ × ℕ) (ULift.{vS} (ℕ × ℕ))
      inferInstance inferInstance e.toRingHom e.symm.toRingHom
      (RingHomInvPair.of_ringEquiv e)
      (RingHomInvPair.of_ringEquiv_symm e)
      ℕ (ULift.{vN} ℕ) inferInstance inferInstance moduleM moduleN :=
    { (AddEquiv.ulift : ULift.{vN} ℕ ≃+ ℕ).symm with
      map_smul' := fun _ _ ↦ rfl }
  let i : ℕ →ₗ[ℕ × ℕ] (ℕ × ℕ) :=
    { toFun := fun m ↦ (m, 0)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change (r.1 * m, 0) = (r.1 * m, r.2 * 0)
        rw [mul_zero] }
  let p : (ℕ × ℕ) →ₗ[ℕ × ℕ] ℕ :=
    { toFun := Prod.fst
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hM : Module.Flat (ℕ × ℕ) ℕ :=
    Module.Flat.of_retract i p (by ext m; rfl)
  exact (Module.Flat.semilinearEquiv_iff e E).mp hM

-- The coefficient homs reduce to the identity; only their proof arguments differ.
example {R : Type uR} {M : Type uM} {N : Type uN}
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (L : M ≃ₗ[R] N) :
    Module.Flat R M ↔ Module.Flat R N := by
  refine ⟨(Module.Flat.semilinearEquiv_iff (RingEquiv.refl R) L).mp, ?_⟩
  intro hN
  let : Module.Flat R N := hN
  exact Module.Flat.of_semilinearEquiv (RingEquiv.refl R) L
