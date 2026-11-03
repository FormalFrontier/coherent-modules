/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The projection kernel of a trivial square-zero extension

The second projection identifies the kernel of the first projection from a trivial
square-zero extension with its coefficient module, semilinearly over the first projection.

## References

The kernel argument comes from the Noetherian criterion for trivial square-zero extensions
in this library, using Mathlib's construction of trivial square-zero extensions.
-/

@[expose] public section

universe uR uM

namespace TrivSqZeroExt

/-- The second projection on the kernel of the first projection of a trivial square-zero
extension, semilinear over the first projection. -/
def kerFstHomSnd (R : Type uR) (M : Type uM) [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    RingHom.ker (fstHom ℕ R M : TrivSqZeroExt R M →+* R) →ₛₗ[
      (fstHom ℕ R M : TrivSqZeroExt R M →+* R)] M :=
  { toFun := fun x ↦ x.val.snd
    map_add' := fun x y ↦ snd_add x.val y.val
    map_smul' := by
      intro a x
      have hx : x.val.fst = 0 := x.property
      change (a * x.val).snd = a.fst • x.val.snd
      simp [snd_mul, hx] }

variable (R : Type uR) (M : Type uM) [Semiring R] [AddCommMonoid M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

/-- The semilinear map from the projection kernel returns the second coordinate. -/
@[simp] theorem kerFstHomSnd_apply
    (x : RingHom.ker (fstHom ℕ R M : TrivSqZeroExt R M →+* R)) :
    kerFstHomSnd R M x = x.val.snd := rfl

/-- The second coordinate determines an element of the projection kernel. -/
theorem kerFstHomSnd_injective : Function.Injective (kerFstHomSnd R M) := by
  intro x y h
  apply Subtype.ext
  apply TrivSqZeroExt.ext
  · have hx : x.val.fst = 0 := x.property
    have hy : y.val.fst = 0 := y.property
    exact hx.trans hy.symm
  · exact h

/-- Every coefficient occurs as the second coordinate of an element of the projection kernel. -/
theorem kerFstHomSnd_surjective : Function.Surjective (kerFstHomSnd R M) := by
  intro m
  exact ⟨⟨inr m, rfl⟩, rfl⟩

/-- The second projection identifies the projection kernel with the coefficient module. -/
theorem kerFstHomSnd_bijective : Function.Bijective (kerFstHomSnd R M) :=
  ⟨kerFstHomSnd_injective R M, kerFstHomSnd_surjective R M⟩

end TrivSqZeroExt
