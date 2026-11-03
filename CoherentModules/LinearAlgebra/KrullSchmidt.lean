/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.DirectSum.Range
public import CoherentModules.LinearAlgebra.End.Local
import HomologicalAlgebra.Abelian.FiniteLengthCancellation
import HomologicalAlgebra.Indecomposable.Artinian
import HomologicalAlgebra.Indecomposable.Noetherian
import HomologicalAlgebra.ModuleCat.Subobject
import HomologicalAlgebra.Preadditive.BiproductUniqueness
import HomologicalAlgebra.ShortComplex.ModuleCatNoetherian
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Internal Krull–Schmidt decompositions of modules

Over an arbitrary ring, a Noetherian module or an Artinian module is a finite
internal direct sum of nonzero indecomposable submodules. These are separate
existence assertions; neither chain condition alone is used to assert locality
of the summands' endomorphism rings.

Two supplied finite internal decompositions with local `Module.End` rings and
linearly equivalent totals have isomorphic summands after an equivalence of
index types. The matching is existential: it need not be unique, and the given
total equivalence need not preserve the displayed submodules. For indecomposable
summands, finite length of one total supplies the required local endomorphism
rings. A common finite-length module also cancels from a product, without any
chain condition on the remaining factors.

The existence witnesses pair each submodule's explicit nonzero fact `A i ≠ ⊥`
with `CategoryTheory.Indecomposable (ModuleCat.of R (A i))`. Both matching
conclusions expose nonzero facts for each supplied family alongside the index
and summand equivalences; these facts follow from the canonical indecomposability
or local-endomorphism hypotheses, without additional assumptions. Zero modules,
including modules over a zero ring, have the empty decomposition. There is no
chosen decomposition or matching instance.

## Implementation notes

The existence and matching assertions realize the corresponding categorical
biproduct results through `ModuleCat` and the direct-sum comparison maps.
Finite families can be reindexed to `Fin` before using small-index comparisons;
`ULift.moduleEquiv` places different carrier universes in a common module
category. Generic supplied-family matching uses the caller's `DecidableEq`
instances on both index types, while existence uses the stock equality instance
on `Fin n`. Empty indices are allowed. The index universes and all carrier
universes remain independent.

## References

* `HomologicalAlgebra.Indecomposable.Artinian` and
  `HomologicalAlgebra.Indecomposable.Noetherian`, for the separate categorical
  existence theorems.
* `HomologicalAlgebra.ModuleCat.Subobject` and
  `HomologicalAlgebra.ShortComplex.ModuleCatNoetherian`, for the module
  chain-condition comparisons.
* `HomologicalAlgebra.Preadditive.BiproductUniqueness`, for local-endomorphism
  Krull–Schmidt uniqueness with supplied finite biproducts.
* `CoherentModules.LinearAlgebra.End.Local`, for locality of `Module.End` of an
  indecomposable finite-length module.
* `HomologicalAlgebra.Abelian.FiniteLengthCancellation`, for cancellation with
  both chain conditions only on the common factor.
* Mathlib's `ModuleCat.coprodIsoDirectSum`, `ModuleCat.biprodIsoProd` and
  `ModuleCat.endRingEquiv`, for the concrete realizations and endomorphism rings.
-/

@[expose] public section

universe uR uI uJ uM uN uP

open scoped DirectSum

namespace Submodule

variable (R : Type uR) [Ring R]
variable (M : Type uM) [AddCommGroup M] [Module R M]

private theorem ne_bot_of_nontrivial_end (A : Submodule R M)
    [Nontrivial (Module.End R A)] : A ≠ ⊥ := by
  intro hA
  have : Subsingleton A := Submodule.subsingleton_iff_eq_bot.mpr hA
  apply one_ne_zero (α := Module.End R A)
  exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _

open CategoryTheory CategoryTheory.Limits in
private theorem exists_isInternal_indecomposable_of_iso_biproduct
    {n : ℕ} (F : Fin n → ModuleCat.{uM} R)
    (hF : ∀ i, CategoryTheory.Indecomposable (F i))
    (d : ModuleCat.of R M ≅ ⨁ F) :
    ∃ A : Fin n → Submodule R M,
      DirectSum.IsInternal A ∧
        ∀ i, A i ≠ ⊥ ∧ CategoryTheory.Indecomposable (ModuleCat.of R (A i)) := by
  let c : ModuleCat.of R M ≅ ModuleCat.of R (⨁ i, F i) :=
    d ≪≫ biproduct.isoCoproduct F ≪≫ ModuleCat.coprodIsoDirectSum F
  let e : (⨁ i, F i) ≃ₗ[R] M := c.symm.toLinearEquiv
  let A : Fin n → Submodule R M := fun i ↦
    LinearMap.range (e.toLinearMap.comp (DirectSum.lof R (Fin n) (fun j ↦ F j) i))
  refine ⟨A, DirectSum.isInternal_range_comp_lof (R := R) (ι := Fin n)
    (A := fun i ↦ (F i : Type uM)) (M := M) e, ?_⟩
  intro i
  have hinj : Function.Injective
      (e.toLinearMap.comp (DirectSum.lof R (Fin n) (fun j ↦ F j) i)) :=
    e.injective.comp (DirectSum.of_injective (β := fun j ↦ F j) i)
  let f : F i ≃ₗ[R] A i := LinearEquiv.ofInjective _ hinj
  have hInd : CategoryTheory.Indecomposable (ModuleCat.of R (A i)) :=
    (CategoryTheory.indecomposable_iff_of_iso f.toModuleIso).1 (hF i)
  refine ⟨?_, hInd⟩
  intro hAi
  exact hInd.1 (ModuleCat.isZero_of_iff_subsingleton.mpr
    (Submodule.subsingleton_iff_eq_bot.mpr hAi))

/-- A Noetherian module over any ring is a finite internal direct sum of nonzero
indecomposable submodules. This realizes
`CategoryTheory.exists_finite_indecomposable_biproduct_of_isNoetherianObject`
as submodules of the original module. Each witness includes `A i ≠ ⊥` alongside
categorical indecomposability. The zero module has the empty family. -/
theorem exists_fin_isInternal_indecomposable_of_isNoetherian [IsNoetherian R M] :
    ∃ n : ℕ, ∃ A : Fin n → Submodule R M,
      DirectSum.IsInternal A ∧
        ∀ i, A i ≠ ⊥ ∧ CategoryTheory.Indecomposable (ModuleCat.of R (A i)) := by
  have : CategoryTheory.IsNoetherianObject (ModuleCat.of R M) :=
    (ModuleCat.isNoetherianObject_iff (ModuleCat.of R M)).2 inferInstance
  obtain ⟨n, F, hF, ⟨d⟩⟩ :=
    CategoryTheory.exists_finite_indecomposable_biproduct_of_isNoetherianObject
      (ModuleCat.of R M)
  exact ⟨n, exists_isInternal_indecomposable_of_iso_biproduct R M F hF d⟩

/-- An Artinian module over any ring is a finite internal direct sum of nonzero
indecomposable submodules. This realizes
`CategoryTheory.exists_finite_indecomposable_biproduct_of_isArtinianObject`
as submodules of the original module. Each witness includes `A i ≠ ⊥` alongside
categorical indecomposability. No Noetherianity is required, and the zero module
has the empty family. -/
theorem exists_fin_isInternal_indecomposable_of_isArtinian [IsArtinian R M] :
    ∃ n : ℕ, ∃ A : Fin n → Submodule R M,
      DirectSum.IsInternal A ∧
        ∀ i, A i ≠ ⊥ ∧ CategoryTheory.Indecomposable (ModuleCat.of R (A i)) := by
  have : CategoryTheory.IsArtinianObject (ModuleCat.of R M) :=
    (ModuleCat.isArtinianObject_iff (ModuleCat.of R M)).2 inferInstance
  obtain ⟨n, F, hF, ⟨d⟩⟩ :=
    CategoryTheory.exists_finite_indecomposable_biproduct_of_isArtinianObject
      (ModuleCat.of R M)
  exact ⟨n, exists_isInternal_indecomposable_of_iso_biproduct R M F hF d⟩

end Submodule

namespace DirectSum.IsInternal

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {ι : Type uI} {κ : Type uJ} [DecidableEq ι] [DecidableEq κ]
variable [Finite ι] [Finite κ]
variable {A : ι → Submodule R M} {B : κ → Submodule R N}

/-- Two supplied finite internal decompositions with local endomorphism rings and
linearly equivalent totals have linearly equivalent factors after reindexing.
This is the concrete-module realization of
`CategoryTheory.exists_equiv_of_iso_biproduct_of_isLocalRing_end`.
The conclusion supplies explicit nonzero facts for both submodule families,
derived from locality, and uses the caller's equality instances on the indices.
The total equivalence is not required to carry a displayed submodule onto a
matched submodule. -/
theorem exists_equiv_of_linearEquiv_of_isLocalRing_end
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B)
    [∀ i, IsLocalRing (Module.End R (A i))]
    [∀ j, IsLocalRing (Module.End R (B j))] (e : M ≃ₗ[R] N) :
    (∀ i, A i ≠ ⊥) ∧ (∀ j, B j ≠ ⊥) ∧
      ∃ σ : ι ≃ κ, ∀ i, Nonempty ((A i) ≃ₗ[R] (B (σ i))) := by
  refine ⟨fun i ↦ Submodule.ne_bot_of_nontrivial_end R M (A i),
    fun j ↦ Submodule.ne_bot_of_nontrivial_end R N (B j), ?_⟩
  -- Include both index universes so the concrete coproducts stay in one category.
  let Y : ι → ModuleCat.{max uM uN uI uJ} R :=
    fun i => ModuleCat.of R (ULift.{max uM uN uI uJ} (A i))
  let Z : κ → ModuleCat.{max uM uN uI uJ} R :=
    fun j => ModuleCat.of R (ULift.{max uM uN uI uJ} (B j))
  let a (i : ι) : Y i ≃ₗ[R] A i := ULift.moduleEquiv
  let b (j : κ) : Z j ≃ₗ[R] B j := ULift.moduleEquiv
  let : CategoryTheory.Limits.HasCoproduct Y :=
    CategoryTheory.Limits.HasColimit.mk
      ⟨ModuleCat.coproductCocone.{uR, uI, max uM uN uI uJ} Y,
        ModuleCat.coproductCoconeIsColimit.{uR, uI, max uM uN uI uJ} Y⟩
  let : CategoryTheory.Limits.HasCoproduct Z :=
    CategoryTheory.Limits.HasColimit.mk
      ⟨ModuleCat.coproductCocone.{uR, uJ, max uM uN uI uJ} Z,
        ModuleCat.coproductCoconeIsColimit.{uR, uJ, max uM uN uI uJ} Z⟩
  let : CategoryTheory.Limits.HasBiproduct Y :=
    CategoryTheory.Limits.HasBiproduct.of_hasCoproduct Y
  let : CategoryTheory.Limits.HasBiproduct Z :=
    CategoryTheory.Limits.HasBiproduct.of_hasCoproduct Z
  have : ∀ i, IsLocalRing (CategoryTheory.End (Y i)) := fun i =>
    ((a i).symm.conjRingEquiv.trans (ModuleCat.endRingEquiv (Y i)).symm).isLocalRing
  have : ∀ j, IsLocalRing (CategoryTheory.End (Z j)) := fun j =>
    ((b j).symm.conjRingEquiv.trans (ModuleCat.endRingEquiv (Z j)).symm).isLocalRing
  let sA : (⨁ i, Y i) ≃ₗ[R] M :=
    (DirectSum.congrLinearEquiv a).trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA)
  let sB : (⨁ j, Z j) ≃ₗ[R] N :=
    (DirectSum.congrLinearEquiv b).trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap B) hB)
  let s : (⨁ i, Y i) ≃ₗ[R] (⨁ j, Z j) := (sA.trans e).trans sB.symm
  let cY : (⨁ Y) ≅ ModuleCat.of R (⨁ i, Y i) :=
    CategoryTheory.Limits.biproduct.isoCoproduct Y ≪≫
      ModuleCat.coprodIsoDirectSum.{uR, uI, max uM uN uI uJ} Y
  let cZ : (⨁ Z) ≅ ModuleCat.of R (⨁ j, Z j) :=
    CategoryTheory.Limits.biproduct.isoCoproduct Z ≪≫
      ModuleCat.coprodIsoDirectSum.{uR, uJ, max uM uN uI uJ} Z
  obtain ⟨σ, hσ⟩ :=
    CategoryTheory.exists_equiv_of_iso_biproduct_of_isLocalRing_end Y Z
      (cY ≪≫ s.toModuleIso ≪≫ cZ.symm)
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨f⟩ := hσ i
  exact ⟨((a i).symm.trans f.toLinearEquiv).trans (b (σ i))⟩

/-- Two supplied finite internal decompositions into indecomposable submodules
of linearly equivalent totals match up to linear equivalence if one total has
finite length. The other total inherits finite length along the supplied
equivalence. The conclusion also supplies explicit nonzero facts for both
submodule families and uses the caller's equality instances on the indices.
Locality of each summand's endomorphism ring is supplied by
`Module.End.isLocalRing_of_indecomposable_of_isFiniteLength`. -/
theorem exists_equiv_of_linearEquiv_of_indecomposable_of_isFiniteLength
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B)
    (hIndA : ∀ i, CategoryTheory.Indecomposable (ModuleCat.of R (A i)))
    (hIndB : ∀ j, CategoryTheory.Indecomposable (ModuleCat.of R (B j)))
    (hLength : IsFiniteLength R M) (e : M ≃ₗ[R] N) :
    (∀ i, A i ≠ ⊥) ∧ (∀ j, B j ≠ ⊥) ∧
      ∃ σ : ι ≃ κ, ∀ i, Nonempty ((A i) ≃ₗ[R] (B (σ i))) := by
  have hLengthN : IsFiniteLength R N := e.isFiniteLength hLength
  have : ∀ i, IsLocalRing (Module.End R (A i)) := fun i =>
    Module.End.isLocalRing_of_indecomposable_of_isFiniteLength (hIndA i)
      (hLength.of_injective (A i).subtype_injective)
  have : ∀ j, IsLocalRing (Module.End R (B j)) := fun j =>
    Module.End.isLocalRing_of_indecomposable_of_isFiniteLength (hIndB j)
      (hLengthN.of_injective (B j).subtype_injective)
  exact hA.exists_equiv_of_linearEquiv_of_isLocalRing_end hB e

end DirectSum.IsInternal

namespace LinearEquiv

variable {R : Type uR} [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- A common finite-length module cancels from a product over any ring.
Only the common factor `P` has a finite-length hypothesis; `M` and `N` are
arbitrary, and their carrier universes are independent. This realizes
`CategoryTheory.nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject`
through the binary-biproduct/product comparison in `ModuleCat`. -/
theorem nonempty_of_prod_of_isFiniteLength (hLength : IsFiniteLength R P)
    (e : (P × M) ≃ₗ[R] (P × N)) : Nonempty (M ≃ₗ[R] N) := by
  let P' := ULift.{max uP uM uN} P
  let M' := ULift.{max uP uM uN} M
  let N' := ULift.{max uP uM uN} N
  let p : P' ≃ₗ[R] P := ULift.moduleEquiv
  let m : M' ≃ₗ[R] M := ULift.moduleEquiv
  let n : N' ≃ₗ[R] N := ULift.moduleEquiv
  have hLength' : IsFiniteLength R P' := p.symm.isFiniteLength hLength
  obtain ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hLength'
  let : CategoryTheory.IsNoetherianObject (ModuleCat.of R P') :=
    (ModuleCat.isNoetherianObject_iff _).2 hNoetherian
  let : CategoryTheory.IsArtinianObject (ModuleCat.of R P') :=
    (ModuleCat.isArtinianObject_iff _).2 hArtinian
  let e' : (P' × M') ≃ₗ[R] (P' × N') :=
    ((p.prodCongr m).trans e).trans (p.prodCongr n).symm
  obtain ⟨f⟩ :=
    CategoryTheory.nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject
      (ModuleCat.of R P') (ModuleCat.of R M') (ModuleCat.of R N')
      (ModuleCat.biprodIsoProd (ModuleCat.of R P') (ModuleCat.of R M') ≪≫
        e'.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of R P') (ModuleCat.of R N')).symm)
  exact ⟨(m.symm.trans f.toLinearEquiv).trans n⟩

end LinearEquiv
