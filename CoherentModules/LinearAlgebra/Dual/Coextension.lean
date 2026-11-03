/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.Category.ModuleCat.ChangeOfRings
public import CoherentModules.LinearAlgebra.Dual.End
public import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Opposite coextension and the linear dual

`Module.Dual.coextensionEquiv` identifies coextension of the regular base-ring
module along `R → Aᵐᵒᵖ`, restricted to `R`, with the given linear dual of `A`.
Evaluation is at `op x`. Under this comparison the existing coextension action
of `op a` becomes the named endomorphism `Module.Dual.rightRegularAlgHom R A (op a)`.

The construction reuses Mathlib's coextension equivalence and opposite dual map.
It installs no opposite-algebra module structure on the dual. The base and algebra
universes are independent; no finiteness or nondegeneracy assumptions are needed.
-/

@[expose] public section

universe uR uA

open MulOpposite

namespace Module.Dual

variable (R : Type uR) (A : Type uA) [CommRing R] [Ring A] [Algebra R A]

/-- Coextension along the opposite algebra, restricted to the base, is the linear dual. -/
noncomputable def coextensionEquiv :
    ((ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj
      ((ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj
        (ModuleCat.of R R))) ≃ₗ[R] Module.Dual R A :=
  (ModuleCat.CoextendScalars.restrictEquiv (S := Aᵐᵒᵖ) (ModuleCat.of R R)).trans
    (opLinearEquiv R (M := A)).dualMap

/-- The comparison evaluates the coextended functional at `op x`. -/
@[simp]
theorem coextensionEquiv_apply
    (ψ : (ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj
      ((ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R))) (x : A) :
    coextensionEquiv R A ψ x =
      (ModuleCat.CoextendScalars.equiv (algebraMap R Aᵐᵒᵖ) (ModuleCat.of R R) ψ) (op x) := by
  simp only [coextensionEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    coe_opLinearEquiv]
  exact ModuleCat.CoextendScalars.restrictEquiv_apply (ModuleCat.of R R) ψ (op x)

/-- The inverse comparison evaluates a functional on the unopposite element. -/
@[simp]
theorem equiv_coextensionEquiv_symm_apply (φ : Module.Dual R A) (s : Aᵐᵒᵖ) :
    (ModuleCat.CoextendScalars.equiv (algebraMap R Aᵐᵒᵖ) (ModuleCat.of R R)
      ((coextensionEquiv R A).symm φ)) s = φ (unop s) := by
  simpa only [LinearEquiv.apply_symm_apply, op_unop] using
    (coextensionEquiv_apply R A ((coextensionEquiv R A).symm φ) (unop s)).symm

/-- Restriction of scalars agrees with the original pointwise base action on the dual. -/
theorem coextensionEquiv_smul_apply (r : R)
    (ψ : (ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj
      ((ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R))) (x : A) :
    coextensionEquiv R A (r • ψ) x = r • coextensionEquiv R A ψ x := by
  rw [map_smul, LinearMap.smul_apply]

/-- Translation by a base scalar reads back as the given base action on the dual. -/
theorem coextensionEquiv_algebraMap_smul (r : R)
    (ψ : (ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R)) :
    coextensionEquiv R A (algebraMap R Aᵐᵒᵖ r • ψ) = r • coextensionEquiv R A ψ := by
  have h := (coextensionEquiv R A).map_smul r
    (show (ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj
      ((ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R)) from ψ)
  rw [ModuleCat.restrictScalars.smul_def] at h
  exact h

/-- Opposite coextension translation evaluates on left multiplication in the algebra. -/
theorem coextensionEquiv_op_smul_apply (a : A)
    (ψ : (ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R)) (x : A) :
    coextensionEquiv R A (op a • ψ) x = coextensionEquiv R A ψ (a * x) := by
  calc
    coextensionEquiv R A (op a • ψ) x =
        (ModuleCat.CoextendScalars.equiv (algebraMap R Aᵐᵒᵖ) (ModuleCat.of R R)
          (op a • ψ)) (op x) := coextensionEquiv_apply R A _ x
    _ = (ModuleCat.CoextendScalars.equiv (algebraMap R Aᵐᵒᵖ) (ModuleCat.of R R)
        ψ) (op (a * x)) := by
      rw [map_smul, ModuleCat.CoextendScalars.smul_apply', ← op_mul]
    _ = coextensionEquiv R A ψ (a * x) := (coextensionEquiv_apply R A ψ _).symm

/-- The comparison intertwines coextension with the named right-regular dual operator. -/
theorem coextensionEquiv_op_smul (a : A)
    (ψ : (ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R)) :
    coextensionEquiv R A (op a • ψ) =
      rightRegularAlgHom R A (op a) (coextensionEquiv R A ψ) := by
  ext x
  exact (coextensionEquiv_op_smul_apply R A a ψ x).trans
    (rightRegularAlgHom_apply R A a (coextensionEquiv R A ψ) x).symm

/-- An element kills a coextended functional exactly when the dual vanishes on its right ideal. -/
theorem coextension_op_smul_eq_zero_iff (a : A)
    (ψ : (ModuleCat.coextendScalars (algebraMap R Aᵐᵒᵖ)).obj (ModuleCat.of R R)) :
    op a • ψ = 0 ↔ ∀ x : A, coextensionEquiv R A ψ (a * x) = 0 := by
  constructor
  · intro h x
    have hE : coextensionEquiv R A (op a • ψ) = 0 :=
      (congrArg (coextensionEquiv R A) h).trans (coextensionEquiv R A).map_zero
    have hF := (coextensionEquiv_op_smul R A a ψ).symm.trans hE
    exact (rightRegularAlgHom_apply R A a (coextensionEquiv R A ψ) x).symm.trans
      (congrArg (fun φ : Module.Dual R A => φ x) hF)
  · intro h
    have hF : rightRegularAlgHom R A (op a) (coextensionEquiv R A ψ) = 0 := by
      ext x
      exact (rightRegularAlgHom_apply R A a (coextensionEquiv R A ψ) x).trans (h x)
    exact (coextensionEquiv R A).injective
      ((coextensionEquiv_op_smul R A a ψ).trans (hF.trans (coextensionEquiv R A).map_zero.symm))

end Module.Dual
