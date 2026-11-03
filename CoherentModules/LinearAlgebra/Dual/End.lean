/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dual endomorphisms

`Module.End.dualMapAlgHom` bundles the contravariant dual map as an algebra
homomorphism from the opposite endomorphism algebra. Composing with left
multiplication gives `Module.Dual.rightRegularAlgHom`, whose value at `op a`
sends a functional `φ` to the functional `x ↦ φ (a * x)`.

These are named endomorphisms of the original linear dual, with its pointwise
scalar structure. No opposite-algebra module structure on the dual is installed.
-/

@[expose] public section

universe u v

open MulOpposite

namespace Module.End

variable (R : Type u) (M : Type v)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Dualization as an algebra homomorphism from the opposite endomorphism algebra. -/
def dualMapAlgHom : (Module.End R M)ᵐᵒᵖ →ₐ[R] Module.End R (Module.Dual R M) where
  toFun f := f.unop.dualMap
  map_zero' := by
    ext φ x
    simp only [unop_zero, LinearMap.dualMap_apply, LinearMap.zero_apply, map_zero]
  map_one' := by
    simpa only [unop_one, Module.End.one_eq_id] using
      (LinearMap.dualMap_id (R := R) (M₁ := M))
  map_add' f g := by
    ext φ x
    simp only [unop_add, LinearMap.dualMap_apply, LinearMap.add_apply, map_add]
  map_mul' f g := by
    simpa only [unop_mul, Module.End.mul_eq_comp] using
      (LinearMap.dualMap_comp_dualMap f.unop g.unop).symm
  commutes' r := by
    ext φ x
    change φ ((algebraMap R (Module.End R M) r) x) =
      (algebraMap R (Module.End R (Module.Dual R M)) r) φ x
    simp only [Module.algebraMap_end_apply, map_smul, LinearMap.smul_apply]

/-- The endomorphism associated to `op f` is the usual dual map of `f`. -/
@[simp]
theorem dualMapAlgHom_apply (f : Module.End R M) :
    dualMapAlgHom R M (op f) = f.dualMap := rfl

/-- Evaluation of the dual endomorphism is precomposition. -/
theorem dualMapAlgHom_apply_apply (f : Module.End R M) (φ : Module.Dual R M) (x : M) :
    dualMapAlgHom R M (op f) φ x = φ (f x) :=
  LinearMap.dualMap_apply f φ x

/-- Scalars in the opposite endomorphism algebra act by pointwise scaling on the dual. -/
theorem dualMapAlgHom_algebraMap_apply (r : R) (φ : Module.Dual R M) :
    dualMapAlgHom R M (algebraMap R (Module.End R M)ᵐᵒᵖ r) φ = r • φ := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

end Module.End

namespace Module.Dual

variable (R : Type u) (A : Type v)
variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- Right translation on the linear dual, obtained by dualizing left multiplication. -/
def rightRegularAlgHom : Aᵐᵒᵖ →ₐ[R] Module.End R (Module.Dual R A) :=
  (Module.End.dualMapAlgHom R A).comp (AlgHom.op (Algebra.lmul R A))

/-- Right translation by `op a` evaluates a functional on left multiplication by `a`. -/
@[simp]
theorem rightRegularAlgHom_apply (a : A) (φ : Module.Dual R A) (x : A) :
    rightRegularAlgHom R A (op a) φ x = φ (a * x) := by
  change (Algebra.lmul R A a).dualMap φ x = φ (a * x)
  rw [LinearMap.dualMap_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

/-- Right translation by the unit is the identity on the dual. -/
theorem rightRegularAlgHom_one :
    rightRegularAlgHom R A (op (1 : A)) = LinearMap.id := by
  simpa only [op_one, Module.End.one_eq_id] using map_one (rightRegularAlgHom R A)

/-- Composition of right translations reverses the order of multiplication in the algebra. -/
theorem rightRegularAlgHom_comp (a b : A) :
    (rightRegularAlgHom R A (op a)).comp (rightRegularAlgHom R A (op b)) =
      rightRegularAlgHom R A (op (b * a)) := by
  simpa only [Module.End.mul_eq_comp, ← op_mul] using
    (map_mul (rightRegularAlgHom R A) (op a) (op b)).symm

/-- Scalars act by the original pointwise scalar multiplication on the dual. -/
theorem rightRegularAlgHom_algebraMap_apply (r : R) (φ : Module.Dual R A) :
    rightRegularAlgHom R A (algebraMap R Aᵐᵒᵖ r) φ = r • φ := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

end Module.Dual
