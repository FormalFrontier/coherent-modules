/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.TensorProduct.FiniteDetection

/-!
# Tensor reflection of surjectivity with finite cokernel

Tensoring with a module `P` whose maximal-ideal images are proper reflects
surjectivity of linear maps with finitely generated cokernel. Neither flatness
nor finite generation of `P` is required, and the source and target of the map
need not be finitely generated.

The quotient–tensor equivalence identifies the tensor of the cokernel with the
quotient by the range of the tensor map. Finite tensor zero-detection then
recovers the vanishing of the original cokernel.

## References

This uses Mathlib's tensor right exactness by Antoine Chambert-Loir and
quotient–tensor equivalences by Antoine Chambert-Loir and Jujian Zhang, together
with `Module.subsingleton_tensorProduct_iff_of_finite`.
-/

@[expose] public section

open scoped TensorProduct

universe uR uP uM uN

namespace LinearMap

/-- Tensoring with a module whose maximal-ideal images are proper preserves and
reflects surjectivity for linear maps with finitely generated cokernel. No
flatness or finiteness of the tensor factor is required. -/
theorem lTensor_surjective_iff_surjective_of_finite_cokernel
    {R : Type uR} [CommRing R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [Module.Finite R (N ⧸ LinearMap.range f)]
    (hP : ∀ m : Ideal R, m.IsMaximal → m • (⊤ : Submodule R P) ≠ ⊤) :
    Function.Surjective (f.lTensor P) ↔ Function.Surjective f := by
  let := Module.addCommMonoidToAddCommGroup R (M := P)
  constructor
  · intro hf
    have hquot : Subsingleton
        ((P ⊗[R] N) ⧸ range ((range f).subtype.lTensor P)) := by
      apply Submodule.Quotient.subsingleton_iff.mpr
      rw [← lTensor_range P (g := f)]
      exact range_eq_top.mpr hf
    have htensor : Subsingleton (P ⊗[R] (N ⧸ range f)) :=
      (TensorProduct.tensorQuotientEquiv P (range f)).toEquiv.subsingleton_congr.mpr hquot
    exact range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp
      ((Module.subsingleton_tensorProduct_iff_of_finite hP).mp htensor))
  · exact lTensor_surjective P

end LinearMap
