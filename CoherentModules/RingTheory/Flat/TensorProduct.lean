/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Faithful flatness of tensor products

Faithful flatness of a tensor product of modules over a commutative ring is
characterized by faithful flatness of both factors. The modules may lie in
independent universes.

## Proof approach

Associativity identifies tensoring with a tensor product with two successive
tensor operations. Faithfulness of the composite implies faithfulness of the
inner operation; commutativity gives this for both factors. These faithful
operations reflect injectivity, so flatness of the composite descends to each
factor. Conversely, flatness and reflection of nontriviality compose.

## References

The proof uses Mathlib's tensor-product associator and commutor, its flatness
and faithful-flatness criteria, and `LinearMap.ker_eq_bot_of_cancel` to express
reflection of injectivity without restricting the module universes.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.FaithfullyFlat

/-- Zero detection for the inner tensor operation follows from zero detection
for the composite. -/
private theorem zero_of_lTensor_zero_right
    (R : Type u) (C : Type v) (D : Type w)
    [CommRing R] [AddCommGroup C] [AddCommGroup D] [Module R C] [Module R D]
    [Module.FaithfullyFlat R (C ⊗[R] D)]
    {N : Type*} {N' : Type*}
    [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') (hf : f.lTensor D = 0) : f = 0 := by
  apply (Module.FaithfullyFlat.zero_iff_lTensor_zero R (C ⊗[R] D) f).mpr
  simp only [LinearMap.lTensor_tensor, hf, LinearMap.lTensor_zero,
    LinearMap.zero_comp, LinearMap.comp_zero]

/-- A faithfully flat tensor product has a faithfully flat right factor. -/
private theorem right_of_tensorProduct
    (R : Type u) (C : Type v) (D : Type w)
    [CommRing R] [AddCommGroup C] [AddCommGroup D] [Module R C] [Module R D]
    [Module.FaithfullyFlat R (C ⊗[R] D)] : Module.FaithfullyFlat R D := by
  -- Reversing the factors is essential: both tensor operations must detect zero.
  let : Module.FaithfullyFlat R (D ⊗[R] C) :=
    Module.FaithfullyFlat.of_linearEquiv R (C ⊗[R] D) (TensorProduct.comm R D C)
  apply (Module.FaithfullyFlat.iff_zero_iff_lTensor_zero R D).mpr
  refine ⟨?_, fun f ↦ ⟨zero_of_lTensor_zero_right R C D f,
    fun hf ↦ by simp [hf]⟩⟩
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  have hinj : Function.Injective ((f.lTensor D).lTensor C) := by
    intro x y hxy
    apply (TensorProduct.assoc R C D N).symm.injective
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := C ⊗[R] D) f hf
    simpa only [LinearMap.lTensor_tensor, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      congrArg (TensorProduct.assoc R C D N').symm hxy
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot_of_cancel
  intro a b hab
  have habC : a.lTensor C = b.lTensor C := by
    apply LinearMap.ext
    intro x
    apply hinj
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply] using
      DFunLike.congr_fun (congrArg (LinearMap.lTensor C) hab) x
  apply sub_eq_zero.mp
  apply zero_of_lTensor_zero_right R D C (a - b)
  simp only [LinearMap.lTensor_sub, habC, sub_self]

end Module.FaithfullyFlat

/-- A tensor product of modules over a commutative ring is faithfully flat if and only if
both factors are faithfully flat. -/
theorem Module.FaithfullyFlat.tensorProduct_iff
    (R : Type u) (C : Type v) (D : Type w)
    [CommRing R] [AddCommGroup C] [AddCommGroup D] [Module R C] [Module R D] :
    Module.FaithfullyFlat R (C ⊗[R] D) ↔
      Module.FaithfullyFlat R C ∧ Module.FaithfullyFlat R D := by
  constructor
  · intro h
    let : Module.FaithfullyFlat R (C ⊗[R] D) := h
    let : Module.FaithfullyFlat R (D ⊗[R] C) :=
      Module.FaithfullyFlat.of_linearEquiv R (C ⊗[R] D) (TensorProduct.comm R D C)
    exact ⟨Module.FaithfullyFlat.right_of_tensorProduct R D C,
      Module.FaithfullyFlat.right_of_tensorProduct R C D⟩
  · rintro ⟨hC, hD⟩
    let : Module.FaithfullyFlat R C := hC
    let : Module.FaithfullyFlat R D := hD
    apply (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful R (C ⊗[R] D)).mpr
    refine ⟨inferInstance, ?_⟩
    intro N _ _ hN
    let : Nontrivial N := hN
    exact (TensorProduct.assoc R C D N).toEquiv.nontrivial
