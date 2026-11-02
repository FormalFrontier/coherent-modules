/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective

/-!
# Restriction of scalars for projective modules

A module projective over a semiring remains projective over a smaller semiring
when the larger semiring is itself projective over the smaller one.
-/

@[expose] public section

open scoped DirectSum

universe u v w

namespace Module.Projective

variable {R : Type u} {S : Type v} {M : Type w}
  [Semiring R] [Semiring S] [AddCommMonoid M]
  [Module R S] [Module R M] [Module S M]
  [IsScalarTower R S S] [IsScalarTower R S M]

/-- Restriction of scalars preserves projectivity when the larger semiring is
projective over the smaller one. -/
theorem restrictScalars [Module.Projective R S] [Module.Projective S M] :
    Module.Projective R M := by
  classical
  let F := ⨁ _ : M, S
  let π : F →ₗ[S] M :=
    DirectSum.toModule S M M (fun m => LinearMap.toSpanSingleton S M m)
  have hπ : Function.Surjective π := by
    intro m
    refine ⟨DirectSum.lof S M (fun _ => S) m 1, ?_⟩
    exact (DirectSum.toModule_lof S (φ := fun m => LinearMap.toSpanSingleton S M m) m 1).trans
      (one_smul S m)
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective π
    (LinearMap.range_eq_top.mpr hπ)
  refine Module.Projective.of_split (σ.restrictScalars R) (π.restrictScalars R) ?_
  ext m
  exact congrArg (fun f : M →ₗ[S] M => f m) hσ

end Module.Projective
