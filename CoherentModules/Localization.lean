/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents
-/
module

public import CoherentModules.Basic
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Localization of coherent modules

This file proves that coherent modules remain coherent after localization and
that coherence descends from localizations away from a set spanning the unit
ideal.

## Main declarations

* `Module.IsCoherent.of_isLocalizedModule`: coherence is preserved by an
  arbitrary module localization over a commutative ring localization.
* `Module.IsCoherent.localizedModule`: coherence of the canonical localized
  module.
* `Module.IsCoherent.away`: the specialization to localization away from an
  element.
* `Module.IsCoherent.of_localizationSpan'`: coherence descends from arbitrary
  realizations of localizations away from a spanning set.
* `Module.IsCoherent.of_localizationSpan`: the canonical localized-module
  specialization.
-/

@[expose] public section

universe u v w x

open scoped Pointwise

namespace Module.IsCoherent

/-- A localization of a coherent module is coherent.

This applies to any ring and module satisfying the respective localization
universal properties. In particular, it does not require the module localization
map to be surjective. -/
theorem of_isLocalizedModule
    {R : Type u} [CommRing R] (S : Submonoid R)
    {Rₚ : Type v} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
    {M : Type w} [AddCommGroup M] [Module R M]
    {Mₚ : Type x} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ]
    [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f] [Module.IsCoherent R M] :
    Module.IsCoherent Rₚ Mₚ where
  finite := Module.Finite.of_isLocalizedModule S f
  finitePresentation_submodule P hP := by
    classical
    obtain ⟨t, htfinite, htspan⟩ := Submodule.fg_def.mp hP
    let s : Finset Mₚ := htfinite.toFinset
    let T : Finset M := IsLocalizedModule.finsetIntegerMultiple S f s
    let N : Submodule R M := Submodule.span R (T : Set M)
    have hNfg : N.FG := Submodule.fg_span T.finite_toSet
    let _ : Module.IsCoherent R N := Module.IsCoherent.submodule N hNfg
    have hNfp : Module.FinitePresentation Rₚ (N.localized' Rₚ S f) :=
      FinitePresentation.of_isBaseChange (N.toLocalized' Rₚ S f)
        ((isLocalizedModule_iff_isBaseChange S Rₚ _).mp inferInstance)
    have hlocalized : N.localized' Rₚ S f = P := by
      change (Submodule.span R (T : Set M)).localized' Rₚ S f = P
      rw [Submodule.localized'_span]
      rw [IsLocalizedModule.finsetIntegerMultiple_image]
      rw [show (s : Set Mₚ) = t from htfinite.coe_toFinset]
      let y := IsLocalizedModule.commonDenomOfFinset S f s
      have hfun : (fun z : Mₚ ↦ y • z) =
          (fun z : Mₚ ↦ algebraMap R Rₚ (y : R) • z) := by
        funext z
        rw [Submonoid.smul_def, algebraMap_smul]
      have hsmul : y • t = algebraMap R Rₚ (y : R) • t := by
        simpa only [← Set.image_smul] using congrArg (fun g : Mₚ → Mₚ ↦ g '' t) hfun
      rw [hsmul, Submodule.span_smul_eq_of_isUnit]
      · exact htspan
      · exact IsLocalization.map_units Rₚ y
    let e : N.localized' Rₚ S f ≃ₗ[Rₚ] P := LinearEquiv.ofEq _ _ hlocalized
    exact Module.FinitePresentation.of_equiv e

/-- The canonical localization of a coherent module is coherent. -/
instance localizedModule
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Submonoid R) [Module.IsCoherent R M] :
    Module.IsCoherent (Localization S) (LocalizedModule S M) :=
  of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

/-- A coherent module remains coherent after localization away from an element. -/
theorem away
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] (r : R) :
    Module.IsCoherent (Localization.Away r) (LocalizedModule.Away r M) :=
  inferInstance

/-- Coherence descends from arbitrary realizations of localizations away from a
set spanning the unit ideal. -/
theorem of_localizationSpan'
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type w} [∀ (g : s), AddCommGroup (Mₚ g)]
    [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type x} [∀ (g : s), CommRing (Rₚ g)]
    [∀ (g : s), Algebra R (Rₚ g)] [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : s), M →ₗ[R] Mₚ g)
    [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (h : ∀ (g : s), Module.IsCoherent (Rₚ g) (Mₚ g)) :
    Module.IsCoherent R M where
  finite := Module.Finite.of_localizationSpan' s hs f fun g ↦ (h g).finite
  finitePresentation_submodule N hN := by
    apply Module.FinitePresentation.of_localizationSpan'
      (Rₚ := Rₚ) (Mₚ := fun g ↦ N.localized' (Rₚ g) (Submonoid.powers g.val) (f g)) s hs
      (fun g ↦ N.toLocalized' (Rₚ g) (Submonoid.powers g.val) (f g))
    intro g
    let _ : Module.IsCoherent (Rₚ g) (Mₚ g) := h g
    have hNlocalized :
        (N.localized' (Rₚ g) (Submonoid.powers g.val) (f g)).FG :=
      N.localized'_fg (Rₚ g) (Submonoid.powers g.val) (f g) hN
    let _ : Module.IsCoherent (Rₚ g)
        (N.localized' (Rₚ g) (Submonoid.powers g.val) (f g)) :=
      Module.IsCoherent.submodule _ hNlocalized
    infer_instance

/-- Coherence descends from canonical localizations away from a set spanning
the unit ideal. -/
theorem of_localizationSpan
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ (g : s), Module.IsCoherent (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) :
    Module.IsCoherent R M :=
  of_localizationSpan' s hs
    (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.val) M) h

end Module.IsCoherent
