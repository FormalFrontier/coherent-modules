/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.FiniteModuleTransfer
public import Mathlib.Data.ZMod.Basic

/-!
# Finite idealization: finite and zero examples

Examples apply the projection kernel, tensor equivalence, and finite-module
transfer results. The `Subsingleton` isomorphism and descent arguments and
concrete true/false cases are proved independently of those results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open scoped TrivSqZeroExt
open scoped TensorProduct

namespace FiniteIdealizationTest

universe uA uR uM u

/-- Restriction along the algebra map gives the original module its base action,
and hence equips the square-zero extension with an induced algebra structure. -/
example {A : Type uA} [CommRing A] {R : Type uR} [CommRing R] [Algebra A R]
    {M : Type uM} [AddCommGroup M] [Module R M] :
    Nonempty (Algebra A (TrivSqZeroExt R M)) := by
  let : Module A M := Module.compHom M (algebraMap A R)
  let : IsScalarTower A R M :=
    ⟨fun a r m => by
      change (a • r) • m = algebraMap A R a • (r • m)
      rw [Algebra.smul_def]
      exact mul_smul (algebraMap A R a) r m⟩
  let : IsScalarTower A Rᵐᵒᵖ M :=
    ⟨fun a r m => by
      change (a • r.unop) • m = algebraMap A R a • (r.unop • m)
      rw [Algebra.smul_def]
      exact mul_smul (algebraMap A R a) r.unop m⟩
  exact ⟨TrivSqZeroExt.algebra' A R M⟩

/-- The canonical induced base action makes the extension an algebra over
the original base without a user-supplied action on the module. -/
example : ℤ →ₐ[ℤ] TrivSqZeroExt ℤ (ZMod 2) :=
  TrivSqZeroExt.inlAlgHom ℤ ℤ (ZMod 2)

/-- Finite product modules give a finite-type square-zero algebra. -/
example : Algebra.FiniteType ℤ (TrivSqZeroExt ℤ (ZMod 2)) := by
  have : Module.Finite ℤ (TrivSqZeroExt ℤ (ZMod 2)) := by
    change Module.Finite ℤ (ℤ × ZMod 2)
    infer_instance
  exact Module.Finite.finiteType (TrivSqZeroExt ℤ (ZMod 2))

/-- The kernel over a finite torsion module is finite over the entire extension;
no freeness assumption on the module is used. -/
example : Module.Finite (TrivSqZeroExt ℤ (ZMod 2))
    (TrivSqZeroExt.kerIdeal ℤ (ZMod 2)) :=
  TrivSqZeroExt.kerIdeal_finite

/-- A nonzero element of the finite torsion module maps to a nonzero kernel element. -/
example : ((TrivSqZeroExt.kerIdealLinearEquiv (R := ℤ) (M := ZMod 2)).symm 1).val ≠ 0 := by
  rw [TrivSqZeroExt.kerIdealLinearEquiv_symm_apply]
  intro heq
  have h : (1 : ZMod 2) = 0 :=
    TrivSqZeroExt.inr_injective (by simpa only [TrivSqZeroExt.inr_zero] using heq)
  exact one_ne_zero h

local instance : Algebra (TrivSqZeroExt ℕ ℕ) ℕ := TrivSqZeroExt.algebraBase ℕ ℕ

/-- The projection-base-change equivalence has no finiteness hypothesis, as illustrated
over the semiring of naturals. The regular module `ℕ` over `ℕ` is finite. -/
example : TrivSqZeroExt.kerIdealBaseChange (R := ℕ) (M := ℕ)
      ((2 : ℕ) ⊗ₜ[TrivSqZeroExt ℕ ℕ]
        (TrivSqZeroExt.kerIdealLinearEquiv (R := ℕ) (M := ℕ)).symm 3) = 6 := by
  simp

/-- On the regular module, the opposite action and scalar tower agree with
projection base change. -/
example (r s : ℕ) :
    TrivSqZeroExt.kerIdealBaseChange (R := ℕ) (M := ℕ)
      (r ⊗ₜ[TrivSqZeroExt ℕ ℕ]
        (TrivSqZeroExt.kerIdealLinearEquiv (R := ℕ) (M := ℕ)).symm s) =
      r • (MulOpposite.op s • (1 : ℕ)) := by
  rw [TrivSqZeroExt.kerIdealBaseChange_tmul, LinearEquiv.apply_symm_apply]
  rw [← smul_assoc]
  rw [← unop_smul_eq_smul (r • MulOpposite.op s) (1 : ℕ)]
  simpa using mul_comm r s

/-- A zero ring has a zero projection kernel. -/
example : Subsingleton (TrivSqZeroExt.kerIdeal (ZMod 1) (ZMod 1)) := by
  exact ((TrivSqZeroExt.kerIdealLinearEquiv (R := ZMod 1) (M := ZMod 1)).toEquiv
    |>.subsingleton_congr).mpr inferInstance

private def isZeroModule (B : Type u) [CommRing B] [Algebra ℤ B]
    (N : Type u) [AddCommGroup N] [Module B N] : Prop := Subsingleton N

private theorem isZeroModule_iso
    (B C : Type u) [CommRing B] [CommRing C]
    [Algebra ℤ B] [Algebra ℤ C]
    [Algebra.FiniteType ℤ B] [Algebra.FiniteType ℤ C]
    (e : B ≃ₐ[ℤ] C) (N N' : Type u)
    [AddCommGroup N] [AddCommGroup N']
    [Module B N] [Module C N']
    [Module.Finite B N] [Module.Finite C N']
    (g : @LinearEquiv B C _ _ e.toRingEquiv.toRingHom
      e.toRingEquiv.symm.toRingHom
      (RingHomInvPair.of_ringEquiv e.toRingEquiv)
      (RingHomInvPair.of_ringEquiv_symm e.toRingEquiv)
      N N' _ _ _ _) :
    isZeroModule B N ↔ isZeroModule C N' :=
  by
    let : RingHomInvPair e.toRingEquiv.toRingHom
        e.toRingEquiv.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
    let : RingHomInvPair e.toRingEquiv.symm.toRingHom
        e.toRingEquiv.toRingHom := RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
    exact g.toEquiv.subsingleton_congr

private theorem isZeroModule_desc
    (B C : Type u) [CommRing B] [CommRing C]
    [algebraAB : Algebra ℤ B] [algebraAC : Algebra ℤ C]
    [Algebra.FiniteType ℤ B] [Algebra.FiniteType ℤ C]
    [algebraBC : Algebra B C]
    [@IsScalarTower ℤ B C algebraAB.toSMul algebraBC.toSMul algebraAC.toSMul]
    (_hf : Function.Surjective (algebraMap B C))
    (_hsq : (RingHom.ker (algebraMap B C)) ^ 2 = ⊥)
    (N : Type u) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    isZeroModule B N → isZeroModule C (C ⊗[B] N) := by
  intro h
  have : Subsingleton N := h
  change Subsingleton (C ⊗[B] N)
  infer_instance

/-- The property holds for the zero module and fails for a finite nonzero torsion module. -/
example : isZeroModule ℤ (ZMod 1) ∧ ¬ isZeroModule ℤ (ZMod 2) := by
  constructor
  · change Subsingleton (ZMod 1)
    infer_instance
  · intro h
    have : Subsingleton (ZMod 2) := h
    exact one_ne_zero (Subsingleton.elim (1 : ZMod 2) 0)

/-- The transfer implication detects failure of the universal ideal property
from the finite nonzero torsion module. -/
example : ¬ (∀ (B : Type) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] (I : Ideal B), I.FG → isZeroModule B I) := by
  intro h
  have hmodules := (Ideal.ideal_property_iff_module_property isZeroModule
    isZeroModule_iso isZeroModule_desc).mp h
  have htwo : isZeroModule ℤ (ZMod 2) := hmodules ℤ (ZMod 2)
  have : Subsingleton (ZMod 2) := htwo
  exact one_ne_zero (Subsingleton.elim (1 : ZMod 2) 0)

end FiniteIdealizationTest
