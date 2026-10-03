/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

public import CoherentModules
public import Mathlib.Data.ZMod.Basic

/-!
External-use checks for the foundational coherent-module API.
-/

namespace CoherentModulesTest.Basic

universe u v w x

open Module

private theorem finiteOfCoherent (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] : Module.Finite R M := inferInstance

private theorem finitePresentationOfCoherent (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] : Module.FinitePresentation R M := inferInstance

private theorem finiteKernelCriterion (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    Module.IsCoherent R M ↔
      Module.Finite R M ∧
        ∀ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), (LinearMap.ker f).FG :=
  Module.IsCoherent.iff_finite_and_fg_ker

private theorem finiteFreeKernel (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] (n : ℕ) (f : (Fin n → R) →ₗ[R] M) :
    (LinearMap.ker f).FG :=
  (Module.IsCoherent.iff_finite_and_fg_ker.mp (inferInstance : Module.IsCoherent R M)).2 n f

private theorem coherentOfFiniteKernels (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hker : ∀ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), (LinearMap.ker f).FG) :
    Module.IsCoherent R M :=
  Module.IsCoherent.iff_finite_and_fg_ker.mpr ⟨inferInstance, hker⟩

private theorem subsingletonCoherent (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M]
    [Subsingleton M] : Module.IsCoherent R M := inferInstance

private theorem linearEquivalenceCriterion (R : Type u) [Ring R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) : Module.IsCoherent R M ↔ Module.IsCoherent R N :=
  Module.IsCoherent.equiv_iff e

private theorem noetherianRingCoherent (R : Type u) [Ring R] [IsNoetherianRing R] :
    IsCoherentRing R := inferInstance

private theorem productCoherent (R : Type u) [Ring R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M × N) := inferInstance

private theorem rankZeroCoherent (R : Type u) [Ring R] [IsCoherentRing R] :
    Module.IsCoherent R (Fin 0 → R) := inferInstance

private theorem rankZeroKernel (R : Type u) [Ring R] :
    (LinearMap.ker (0 : (Fin 0 → R) →ₗ[R] (Fin 0 → R))).FG :=
  (Module.IsCoherent.iff_finite_and_fg_ker.mp
    (inferInstance : Module.IsCoherent R (Fin 0 → R))).2 0 0

private theorem finiteRankCoherent (R : Type u) [Ring R] [IsCoherentRing R] (n : ℕ) :
    Module.IsCoherent R (Fin n → R) := inferInstance

private theorem finiteFreeCoherent (R : Type u) [Ring R] [IsCoherentRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Module.IsCoherent R M := Module.IsCoherent.of_free R

private theorem rangeCoherent (R : Type u) [Ring R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.range f) := Module.IsCoherent.range f

private theorem extensionCoherent (R : Type u) [Ring R] (M : Type v) (N : Type w) (P : Type x)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.IsCoherent R M] [Module.IsCoherent R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.IsCoherent R N :=
  Module.IsCoherent.of_exact f g h hf hg

private theorem kernelCoherent (R : Type u) [Ring R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.ker f) := Module.IsCoherent.ker f

private theorem kernelFinitePresentation (R : Type u) [Ring R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.FinitePresentation R (LinearMap.ker f) :=
  Module.IsCoherent.finitePresentation_ker f

private theorem quotientCoherent (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] (N : Submodule R M) (hN : N.FG) :
    Module.IsCoherent R (M ⧸ N) :=
  Module.IsCoherent.quotient N hN

private theorem cokernelCoherent (R : Type u) [Ring R] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (N ⧸ LinearMap.range f) :=
  Module.IsCoherent.cokernel f

private theorem bottomQuotientCoherent (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] : Module.IsCoherent R (M ⧸ (⊥ : Submodule R M)) :=
  Module.IsCoherent.quotient ⊥ Submodule.fg_bot

private theorem zeroMapCokernelCoherent (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] :
    Module.IsCoherent R (M ⧸ LinearMap.range (0 : PUnit →ₗ[R] M)) :=
  Module.IsCoherent.cokernel 0

private theorem finiteFreeKernelPresentation (R : Type u) [Ring R] [IsCoherentRing R]
    (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Free R M] [Module.Free R N] [Module.Finite R M] [Module.Finite R N]
    (f : M →ₗ[R] N) : Module.FinitePresentation R (LinearMap.ker f) :=
  Module.finitePresentation_ker_of_free R f

private theorem rankZeroKernelPresentation (R : Type u) [Ring R] [IsCoherentRing R] :
    Module.FinitePresentation R
      (LinearMap.ker (0 : (Fin 0 → R) →ₗ[R] (Fin 0 → R))) :=
  Module.finitePresentation_ker_of_free R _

private theorem zeroRingKernelPresentation : Module.FinitePresentation (ZMod 1)
    (LinearMap.ker (LinearMap.id : ZMod 1 →ₗ[ZMod 1] ZMod 1)) :=
  Module.finitePresentation_ker_of_free (ZMod 1) _

private theorem zeroRingTopQuotient : Module.IsCoherent (ZMod 1)
    (ZMod 1 ⧸ (⊤ : Submodule (ZMod 1) (ZMod 1))) :=
  Module.IsCoherent.quotient ⊤ Module.Finite.fg_top

private theorem zeroRingExtension : Module.IsCoherent (ZMod 1) (ZMod 1) :=
  Module.IsCoherent.of_exact
    (0 : ZMod 1 →ₗ[ZMod 1] ZMod 1) (0 : ZMod 1 →ₗ[ZMod 1] ZMod 1)
    (by
      intro y
      constructor
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩
      · intro _
        exact Subsingleton.elim _ _)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun y ↦ ⟨0, Subsingleton.elim _ y⟩)

private theorem zeroRingFiniteKernel :
    (LinearMap.ker (0 : (Fin 0 → ZMod 1) →ₗ[ZMod 1] ZMod 1)).FG :=
  (Module.IsCoherent.iff_finite_and_fg_ker.mp
    (inferInstance : Module.IsCoherent (ZMod 1) (ZMod 1))).2 0 0

/-- A zero map from a rank-one free module has a finite kernel without being surjective. -/
public theorem nonSurjectiveFiniteKernel :
    (LinearMap.ker (0 : (Fin 1 → ℤ) →ₗ[ℤ] ℤ)).FG ∧
      ¬Function.Surjective (0 : (Fin 1 → ℤ) →ₗ[ℤ] ℤ) := by
  constructor
  · exact
      (Module.IsCoherent.iff_finite_and_fg_ker.mp
        (inferInstance : Module.IsCoherent ℤ ℤ)).2 1 0
  · intro h
    simpa using h 1

-- Selected named-client axiom checks, not a complete release census.
#print axioms finiteOfCoherent
#print axioms finitePresentationOfCoherent
#print axioms finiteKernelCriterion
#print axioms finiteFreeKernel
#print axioms coherentOfFiniteKernels
#print axioms subsingletonCoherent
#print axioms linearEquivalenceCriterion
#print axioms noetherianRingCoherent
#print axioms productCoherent
#print axioms rankZeroCoherent
#print axioms rankZeroKernel
#print axioms finiteRankCoherent
#print axioms finiteFreeCoherent
#print axioms rangeCoherent
#print axioms extensionCoherent
#print axioms kernelCoherent
#print axioms kernelFinitePresentation
#print axioms quotientCoherent
#print axioms cokernelCoherent
#print axioms bottomQuotientCoherent
#print axioms zeroMapCokernelCoherent
#print axioms finiteFreeKernelPresentation
#print axioms rankZeroKernelPresentation
#print axioms zeroRingKernelPresentation
#print axioms zeroRingTopQuotient
#print axioms zeroRingExtension
#print axioms zeroRingFiniteKernel
#print axioms nonSurjectiveFiniteKernel

end CoherentModulesTest.Basic
