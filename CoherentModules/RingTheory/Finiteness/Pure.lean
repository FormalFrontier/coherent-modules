/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite generation and presentation under scalar extension

Injectivity of the tensor unit reflects finite generation and finite
presentation. The coefficient ring is commutative, but the scalar algebra need
not be. No flatness of the scalar algebra is assumed. The module may be only an
additive commutative monoid, and its universe is independent of both rings.

## References

The finite-generation argument generalizes Mathlib's faithfully-flat descent
argument. The proofs use Mathlib's finite-presentation, submodule scalar-extension
and tensor right-exactness APIs.
-/

@[expose] public section

universe uR uS uM

open scoped TensorProduct

namespace Module.Finite

/-- Finite generation descends when the tensor unit is injective on modules in
the indicated test universe. No flatness or commutativity of `S` is required. -/
theorem of_finite_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [Semiring S] [Algebra R S]
    [Module.Finite S (S ⊗[R] M)]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.Finite R M := by
  apply Module.Finite.of_fg_top
  apply (Submodule.fg_baseChange_iff_of_injective hunit (⊤ : Submodule R M)).mp
  simpa only [Submodule.baseChange_top] using
    (Module.Finite.fg_top (R := S) (M := S ⊗[R] M))

/-- Finite generation is invariant under scalar extension with injective tensor
units. The scalar algebra need not be commutative or flat. -/
theorem iff_finite_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [Semiring S] [Algebra R S]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.Finite S (S ⊗[R] M) ↔ Module.Finite R M := by
  constructor
  · intro h
    let : Module.Finite S (S ⊗[R] M) := h
    exact of_finite_tensorProduct_of_injective R M S hunit
  · intro h
    let : Module.Finite R M := h
    exact Module.Finite.base_change R S M

end Module.Finite

namespace Module.FinitePresentation

/-- Finite presentation descends when the tensor unit is injective on modules in
the indicated test universe. No flatness or commutativity of `S` is required. -/
theorem of_finitePresentation_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [Ring S] [Algebra R S]
    [Module.FinitePresentation S (S ⊗[R] M)]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.FinitePresentation R M := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : Module.Finite S (S ⊗[R] M) := inferInstance
  let : Module.Finite R M :=
    Module.Finite.of_finite_tensorProduct_of_injective R M S hunit
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  -- This is the free module on the chosen generators, in the test universe.
  let D : Type (max uR uM) := s →₀ R
  -- Retain the monoid and module data used by the linear-combination map.
  let : AddCommGroup D := Module.addCommMonoidToAddCommGroup R
  let f : D →ₗ[R] M := Finsupp.linearCombination R ((↑) : s → M)
  let K : Submodule R D := LinearMap.ker f
  have hf : Function.Surjective f := by
    apply (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination
      (R := R) (v := ((↑) : s → M))).mp
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
  let : Module.Free R D := inferInstance
  let : Module.FinitePresentation R D := inferInstance
  let : Module.Finite R D := inferInstance
  let : Module.Finite S (S ⊗[R] D) := Module.Finite.base_change R S D
  -- Right exactness identifies the kernel with an image, not with S ⊗ K.
  have hexact : Function.Exact (K.subtype.baseChange S) (f.baseChange S) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (_root_.lTensor_exact (R := R) (M := K) (N := D) (P := M)
        (f := K.subtype) (g := f) S f.exact_subtype_ker_map hf)
  have hker : LinearMap.ker (f.baseChange S) = K.baseChange S :=
    LinearMap.exact_iff.mp hexact
  have hKbase : (K.baseChange S).FG := by
    rw [← hker]
    exact Module.FinitePresentation.fg_ker (f.baseChange S)
      (LinearMap.baseChange_surjective S hf)
  have hK : K.FG :=
    (Submodule.fg_baseChange_iff_of_injective (M := D) hunit K).mp hKbase
  exact ⟨s, hs, hK⟩

/-- Finite presentation is invariant under scalar extension with injective tensor
units. The scalar algebra need not be commutative or flat. -/
theorem iff_finitePresentation_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [Ring S] [Algebra R S]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.FinitePresentation S (S ⊗[R] M) ↔ Module.FinitePresentation R M := by
  constructor
  · intro h
    let : Module.FinitePresentation S (S ⊗[R] M) := h
    exact of_finitePresentation_tensorProduct_of_injective R M S hunit
  · intro h
    classical
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    obtain ⟨s, hs, hK⟩ := h.out
    let D : Type (max uR uM) := s →₀ R
    let : AddCommGroup D := Module.addCommMonoidToAddCommGroup R
    let f : D →ₗ[R] M := Finsupp.linearCombination R ((↑) : s → M)
    let K : Submodule R D := LinearMap.ker f
    have hf : Function.Surjective f := by
      apply (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination
        (R := R) (v := ((↑) : s → M))).mp
      simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
    let : Module.Free R D := inferInstance
    let : Module.Finite R D := inferInstance
    let : Module.Free S (S ⊗[R] D) := inferInstance
    let : Module.Finite S (S ⊗[R] D) := Module.Finite.base_change R S D
    have hexact : Function.Exact (K.subtype.baseChange S) (f.baseChange S) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using
        (_root_.lTensor_exact (R := R) (M := K) (N := D) (P := M)
          (f := K.subtype) (g := f) S f.exact_subtype_ker_map hf)
    have hker : LinearMap.ker (f.baseChange S) = K.baseChange S :=
      LinearMap.exact_iff.mp hexact
    -- Only the image of the tensored relation module needs to be finite.
    let : Module.Finite R K := Module.Finite.of_fg (show K.FG from hK)
    let : Module.Finite S (S ⊗[R] K) := Module.Finite.base_change R S K
    let : Module.Finite S (K.baseChange S) :=
      Module.Finite.of_surjective (K.toBaseChange S)
        (Submodule.toBaseChange_surjective S K)
    apply Module.finitePresentation_of_free_of_surjective (f.baseChange S)
      (LinearMap.baseChange_surjective S hf)
    rw [hker]
    exact Module.Finite.iff_fg.mp (inferInstance : Module.Finite S (K.baseChange S))

end Module.FinitePresentation
