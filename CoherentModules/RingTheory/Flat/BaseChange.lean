/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.Localization
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Flat scalar extension, faithful actions and faithful flatness

Flat scalar extension carries the kernel ideal of an algebra homomorphism to the
kernel ideal of its tensor product with the identity. The scalar algebra and both
original algebras may be noncommutative; only the coefficient ring is commutative.

A commutative algebra covers every maximal ideal of its coefficient ring if and
only if scalar extension reflects faithful flatness for every originally flat
module. Preservation of faithful flatness holds for arbitrary base change.
The tensor product has the canonical action on its left factor; the original
module needs no action of the scalar algebra.

Flat scalar extension also preserves the faithful action of a finite module, without
requiring that original module to be flat. The coefficient semiring is commutative,
but the scalar algebra need not be commutative, and the module may be an additive
commutative monoid. The three universes are independent.

In the maximal-ideal criterion, the test modules have carrier universe `max u w`,
where `u` is the coefficient ring's universe and `w` is arbitrary. The scalar
algebra's universe is independent.
This allows the converse to test the direct sum of principal localizations indexed
by all elements of a maximal ideal, raised by `ULift` if necessary. No finite
generation of that ideal or flatness of the scalar algebra is required.

## References

The kernel formula combines Mathlib's `Module.Flat.ker_lTensor_eq` with
`TensorProduct.AlgebraTensorModule.range_lTensor_idealMap`.

The proof uses the sufficient criterion
`Module.FaithfullyFlat.iff_flat_and_baseChange_of_map_maximal_ne_top` and the
principal-localization criterion `Module.FaithfullyFlat.directSum_away_iff`.
It combines Mathlib's `TensorProduct.directSumRight`,
`DirectSum.congrLinearEquiv` and `IsLocalization.Away.tensorEquiv` to identify the
base change of the direct sum, and uses Mathlib's linear-equivalence and `ULift`
transport for flatness and faithful flatness.

Faithful-action preservation uses Mathlib's finite generating families,
`LinearMap.ext_on_range`, `Module.Flat.lTensor_preserves_injective_linearMap`,
the right tensor unitor and the finite-product comparison `TensorProduct.piRight`.
-/

@[expose] public section

universe u v w

open scoped DirectSum TensorProduct

namespace Algebra

/-- Every maximal ideal of `R` extends to a proper ideal of `S` if and only if
faithful flatness is preserved and reflected by scalar extension on every flat
`R`-module with carrier in `Type (max u w)`. The tensor product uses its canonical
left-factor `S`-action, with no `S`-action on the original module. The universe of
`S` is independent, and no flatness or surjectivity of the scalar map, finiteness,
Noetherianity, locality or nontriviality hypothesis is needed. -/
theorem map_maximal_ne_top_iff_forall_faithfullyFlat_baseChange
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] :
    (∀ m : Ideal R, m.IsMaximal →
      m.map (algebraMap R S) ≠ ⊤) ↔
      ∀ (M : Type (max u w)) [AddCommGroup M] [Module R M],
        Module.Flat R M →
          (Module.FaithfullyFlat R M ↔
            Module.FaithfullyFlat S (S ⊗[R] M)) := by
  constructor
  · intro hmax M _ _ hflat
    exact (Module.FaithfullyFlat.iff_flat_and_baseChange_of_map_maximal_ne_top hmax).trans
      (and_iff_right hflat)
  · intro h m hm hmap
    classical
    let A := fun r : m ↦ Localization.Away (r : R)
    let D := ⨁ r : m, A r
    have hrange : Set.range (fun r : m ↦ (r : R)) = (m : Set R) := by
      ext r
      exact ⟨fun ⟨s, hs⟩ ↦ hs ▸ s.property, fun hr ↦ ⟨⟨r, hr⟩, rfl⟩⟩
    have hspan : Ideal.span (Set.range (fun r : m ↦ (r : R))) = m := by
      rw [hrange, Ideal.span_eq]
    have hspanS : Ideal.span (Set.range (fun r : m ↦ algebraMap R S (r : R))) = ⊤ := by
      rw [Set.range_comp', ← Ideal.map_span, hspan, hmap]
    have : Module.FaithfullyFlat S
        (⨁ r : m, Localization.Away (algebraMap R S (r : R))) :=
      (Module.FaithfullyFlat.directSum_away_iff S _).mpr hspanS
    let e : (S ⊗[R] D) ≃ₗ[S]
        (⨁ r : m, Localization.Away (algebraMap R S (r : R))) :=
      (_root_.TensorProduct.directSumRight R S S A).trans
        (DirectSum.congrLinearEquiv fun r ↦
          (IsLocalization.Away.tensorEquiv (R := R) (r := (r : R)) (A := A r) S).toLinearEquiv)
    have : Module.FaithfullyFlat S (S ⊗[R] D) :=
      Module.FaithfullyFlat.of_linearEquiv S _ e
    let eLift : ULift.{w} D ≃ₗ[R] D := ULift.moduleEquiv
    have : Module.FaithfullyFlat S (S ⊗[R] ULift.{w} D) :=
      Module.FaithfullyFlat.of_linearEquiv S _ (eLift.baseChange R S)
    have : ∀ r : m, Module.Flat R (A r) := fun r ↦
      IsLocalization.flat (A r) (Submonoid.powers (r : R))
    have hflat : Module.Flat R (ULift.{w} D) := inferInstance
    have : Module.FaithfullyFlat R (ULift.{w} D) := (h _ hflat).mpr inferInstance
    have hD : Module.FaithfullyFlat R D :=
      Module.FaithfullyFlat.of_linearEquiv R _ eLift.symm
    exact hm.ne_top (hspan ▸ (Module.FaithfullyFlat.directSum_away_iff R _).mp hD)

/-! ## Kernels under flat scalar extension -/

namespace TensorProduct

universe uR uS uA uB

/-- If `S` is flat over `R`, the kernel left ideal of `id_S ⊗ f` is generated by
`ker f` under the right-factor inclusion. The algebra `S` need not be commutative. -/
theorem ker_map_id_left
    {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
    [CommRing R] [Ring S] [Ring A] [Ring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Module.Flat R S]
    (f : A →ₐ[R] B) :
    RingHom.ker (map (AlgHom.id R S) f) =
      (RingHom.ker f).map (includeRight : A →ₐ[R] S ⊗[R] A) := by
  apply (Submodule.restrictScalars_injective R _ _)
  exact (Module.Flat.ker_lTensor_eq R S f.toLinearMap).trans
    (_root_.TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
      (R := R) (A := S) R (RingHom.ker f))

end TensorProduct

end Algebra

/-- A finite faithful module remains faithful after flat scalar extension, with the
canonical left-factor action on the tensor product. The scalar algebra may be
noncommutative and the module need not be flat. For semirings, `Module.Flat` has
Mathlib's mono-flat meaning. -/
theorem FaithfulSMul.baseChange_of_finite_of_flat
    (C : Type u) (S : Type v) (N : Type w)
    [CommSemiring C] [Semiring S] [Algebra C S]
    [AddCommMonoid N] [Module C N]
    [Module.Finite C N] [FaithfulSMul C N] [Module.Flat C S] :
    FaithfulSMul S (S ⊗[C] N) := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := C) (M := N)
  let f : C →ₗ[C] (Fin n → N) :=
    LinearMap.pi fun i ↦ LinearMap.toSpanSingleton C N (v i)
  have hf : Function.Injective f := by
    intro a b hab
    apply eq_of_smul_eq_smul (α := N)
    have he : a • (LinearMap.id : N →ₗ[C] N) = b • LinearMap.id :=
      LinearMap.ext_on_range hv fun i ↦ congrFun hab i
    exact fun x ↦ congrArg (fun g : N →ₗ[C] N ↦ g x) he
  have hfS : Function.Injective (f.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  refine ⟨?_⟩
  intro s t h
  apply (TensorProduct.rid C S).symm.injective
  apply hfS
  apply (TensorProduct.piRight C C S (fun _ : Fin n ↦ N)).injective
  funext i
  simpa [f, TensorProduct.smul_tmul', smul_eq_mul] using h (1 ⊗ₜ[C] v i)
