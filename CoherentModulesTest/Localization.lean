/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

import CoherentModules
import Mathlib.Data.ZMod.Basic

/-!
External-use checks for coherent-module localization and descent.
-/

namespace CoherentModulesTest.Localization

universe u v w x

open Module

private theorem arbitraryLocalization {R : Type u} [CommRing R] (S : Submonoid R)
    {Rₚ : Type v} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
    {M : Type w} [AddCommGroup M] [Module R M]
    {Mₚ : Type x} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ]
    [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f] [Module.IsCoherent R M] :
    Module.IsCoherent Rₚ Mₚ :=
  Module.IsCoherent.of_isLocalizedModule S f

private theorem canonicalLocalization {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] (S : Submonoid R) :
    Module.IsCoherent (Localization S) (LocalizedModule S M) :=
  inferInstance

private theorem awayLocalization {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] (r : R) :
    Module.IsCoherent (Localization.Away r) (LocalizedModule.Away r M) :=
  Module.IsCoherent.away r

private theorem arbitrarySpanningDescent {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type w} [∀ (g : s), AddCommGroup (Mₚ g)]
    [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type x} [∀ (g : s), CommRing (Rₚ g)]
    [∀ (g : s), Algebra R (Rₚ g)] [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : s), M →ₗ[R] Mₚ g)
    [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (h : ∀ (g : s), Module.IsCoherent (Rₚ g) (Mₚ g)) :
    Module.IsCoherent R M :=
  Module.IsCoherent.of_localizationSpan' s hs f h

private theorem canonicalSpanningDescent {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ (g : s), Module.IsCoherent (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) :
    Module.IsCoherent R M :=
  Module.IsCoherent.of_localizationSpan s hs h

private theorem zeroRingAway : Module.IsCoherent (Localization.Away (0 : ZMod 1))
    (LocalizedModule.Away (0 : ZMod 1) (ZMod 1)) :=
  Module.IsCoherent.away 0

private theorem rankZeroLocalization (R : Type u) [CommRing R] [IsCoherentRing R] (S : Submonoid R) :
    Module.IsCoherent (Localization S) (LocalizedModule S (Fin 0 → R)) :=
  inferInstance

private theorem emptySpanningSet : Module.IsCoherent (ZMod 1) (Fin 0 → ZMod 1) := by
  apply Module.IsCoherent.of_localizationSpan (∅ : Set (ZMod 1))
  · rw [Ideal.span_empty]
    exact Subsingleton.elim _ _
  · rintro ⟨g, hg⟩
    simp at hg

-- Selected named-client axiom checks, not a complete release census.
#print axioms arbitraryLocalization
#print axioms canonicalLocalization
#print axioms awayLocalization
#print axioms arbitrarySpanningDescent
#print axioms canonicalSpanningDescent
#print axioms zeroRingAway
#print axioms rankZeroLocalization
#print axioms emptySpanningSet

end CoherentModulesTest.Localization
