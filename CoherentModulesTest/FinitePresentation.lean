/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

public import CoherentModules

/-!
External-use checks for the finite-presentation/coherence bridge.
-/

namespace CoherentModulesTest.FinitePresentation

universe u v w v1 v2 v3 v4 v5

private theorem coherentOfFinitePresentation (R : Type u) [Ring R] [IsCoherentRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] : Module.IsCoherent R M :=
  Module.FinitePresentation.isCoherent

private theorem coherenceCriterion (R : Type u) [Ring R] [IsCoherentRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.IsCoherent R M ↔ Module.FinitePresentation R M :=
  Module.isCoherent_iff_finitePresentation

private theorem kernelPresentation (R : Type u) [Ring R] [IsCoherentRing R]
    (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) : Module.FinitePresentation R (LinearMap.ker f) :=
  Module.FinitePresentation.ker f

private theorem integerProjectionKernel : Module.FinitePresentation ℤ
    (LinearMap.ker (LinearMap.fst ℤ ℤ ℤ)) :=
  Module.FinitePresentation.ker (LinearMap.fst ℤ ℤ ℤ)

private theorem exactFivePresentation (R : Type u) [Ring R] [IsCoherentRing R]
    (M1 : Type v1) (M2 : Type v2) (M3 : Type v3)
    (M4 : Type v4) (M5 : Type v5)
    [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2]
    [AddCommGroup M3] [Module R M3]
    [AddCommGroup M4] [Module R M4]
    [AddCommGroup M5] [Module R M5]
    [Module.Finite R M1]
    [Module.FinitePresentation R M2]
    [Module.FinitePresentation R M4]
    [Module.FinitePresentation R M5]
    (f12 : M1 →ₗ[R] M2) (f23 : M2 →ₗ[R] M3)
    (f34 : M3 →ₗ[R] M4) (f45 : M4 →ₗ[R] M5)
    (h2 : Function.Exact f12 f23)
    (h3 : Function.Exact f23 f34)
    (h4 : Function.Exact f34 f45) :
    Module.FinitePresentation R M3 :=
  Module.FinitePresentation.of_exact_five f12 f23 f34 f45 h2 h3 h4

/-- A nonzero five-term sequence with alternating identity and zero maps. -/
public theorem alternatingIdentitySequence : Module.FinitePresentation ℤ ℤ := by
  apply Module.FinitePresentation.of_exact_five
      (LinearMap.id : ℤ →ₗ[ℤ] ℤ) 0
      (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (0 : ℤ →ₗ[ℤ] ℤ)
  all_goals rw [LinearMap.exact_iff]
  all_goals simp

/-- A sequence with zero end modules and exactness at both degenerate edges. -/
private theorem zeroEndSequence : Module.FinitePresentation ℤ ℤ := by
  apply Module.FinitePresentation.of_exact_five
      (0 : (Fin 0 → ℤ) →ₗ[ℤ] (Fin 0 → ℤ))
      (0 : (Fin 0 → ℤ) →ₗ[ℤ] ℤ)
      (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
      (0 : ℤ →ₗ[ℤ] (Fin 0 → ℤ))
  · intro x
    simp [Subsingleton.elim x 0]
  · rw [LinearMap.exact_iff]
    simp
  · rw [LinearMap.exact_iff]
    simp

-- Selected named-client axiom checks, not a complete release census.
#print axioms coherentOfFinitePresentation
#print axioms coherenceCriterion
#print axioms kernelPresentation
#print axioms integerProjectionKernel
#print axioms exactFivePresentation
#print axioms alternatingIdentitySequence
#print axioms zeroEndSequence

end CoherentModulesTest.FinitePresentation
