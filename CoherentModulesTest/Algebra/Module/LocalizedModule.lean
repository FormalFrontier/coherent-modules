/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.Module.LocalizedModule.Finite
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Equality clearing when zero is a denominator

The uniform equality criterion and the finite-source implication identify distinct
endomorphisms after localization when zero belongs to the localizing submonoid.
-/

@[expose] public section

example {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ s : (⊤ : Submonoid R), s • (LinearMap.id : R →ₗ[R] R) = 0 ∧
      (LinearMap.id : R →ₗ[R] R) ≠ 0 := by
  let S : Submonoid R := ⊤
  let f := LocalizedModule.mkLinearMap S R
  have hcomp : f.comp (LinearMap.id : R →ₗ[R] R) =
      f.comp (0 : R →ₗ[R] R) :=
    (IsLocalizedModule.comp_eq_iff_exists_smul_eq S f
      (LinearMap.id : R →ₗ[R] R) (0 : R →ₗ[R] R)).mpr
      ⟨⟨0, by simp [S]⟩, by simp⟩
  obtain ⟨s, hs⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
      S f (LinearMap.id : R →ₗ[R] R) (0 : R →ₗ[R] R) hcomp
  refine ⟨s, ?_, ?_⟩
  · simpa using hs
  · intro h
    have h1 : (1 : R) = 0 := by
      simpa only [LinearMap.id_apply, LinearMap.zero_apply] using
        congrArg (fun k : R →ₗ[R] R => k 1) h
    exact one_ne_zero h1
