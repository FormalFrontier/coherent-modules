/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.FinitePresentation

/-!
# Finite presentations from finite free semimodules

These examples construct finite presentations and then use existing finite-presentation
APIs. For semirings, finite presentation concerns a finite spanning subset and the zero
kernel of its linear-combination map, not a finite relation congruence.

## References

The constructor follows Mathlib's finite-image basis argument in
`Module.finitePresentation_of_free_of_surjective`.
-/

@[expose] public section

universe u v w z

/- The semiring constructor supplies the instance required by the finite-free
zero-fiber exactness eliminator. -/
example {R : Type u} {P : Type v} {M : Type w}
    [Semiring R] [AddCommMonoid P] [AddCommMonoid M] [Module R P] [Module R M]
    [Module.Free R P] [Module.Finite R P]
    (f : P →ₗ[R] M) (hf : Function.Surjective f) (hk : (LinearMap.ker f).FG) :
    ∃ (n m : ℕ) (g : (Fin n → R) →ₗ[R] M)
      (d : (Fin m → R) →ₗ[R] (Fin n → R)),
      Function.Surjective g ∧ Function.Exact d g := by
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_free_of_surjective f hf hk
  exact Module.FinitePresentation.exists_fin_exact R M

/- Over a ring, one finite-free presentation controls the zero kernel of an
independent surjection. The finite-presentation input is for its source Q, not M. -/
example {R : Type u} {P : Type v} {M : Type w} {Q : Type z}
    [Ring R] [AddCommGroup P] [AddCommGroup M] [AddCommGroup Q]
    [Module R P] [Module R M] [Module R Q]
    [Module.Free R P] [Module.Finite R P] [Module.FinitePresentation R Q]
    (f : P →ₗ[R] M) (hf : Function.Surjective f) (hk : (LinearMap.ker f).FG)
    (q : Q →ₗ[R] M) (hq : Function.Surjective q) : (LinearMap.ker q).FG := by
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_free_of_surjective f hf hk
  exact (Module.FinitePresentation.fg_ker_iff (R := R) (M := Q) (N := M) q hq).mpr
    inferInstance
