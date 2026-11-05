/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Restricting scalars in polynomial spans

For compatible actions of a semiring and its polynomial semiring on an additive
commutative monoid, the polynomial span of a family is the scalar span of all its
monomial shifts. The family and both scalar actions are arbitrary; in particular,
the coefficient semiring need not be commutative.

The proof uses Mathlib's `Finsupp.linearCombination_smul` and
`Polynomial.basisMonomials` to factor the linear combination map through a
surjective change of coefficients.
-/

@[expose] public section

universe u v w

namespace Polynomial

variable {R : Type u} {M : Type v} {ι : Type w}
variable [Semiring R] [AddCommMonoid M] [Module R M] [Module R[X] M]
variable [IsScalarTower R R[X] M]

/-- Restricting the polynomial span of a family to the coefficient semiring gives
exactly the span of all monomial shifts of that family. -/
theorem restrictScalars_span_range (g : ι → M) :
    (Submodule.span R[X] (Set.range g)).restrictScalars R =
      Submodule.span R (Set.range (fun p : ι × ℕ => (X ^ p.2 : R[X]) • g p.1)) := by
  suffices h :
      (Submodule.span R[X] (Set.range g)).restrictScalars R =
        Submodule.span R
          (Set.range (fun p : ι × ℕ => basisMonomials R p.2 • g p.1)) by
    simpa only [coe_basisMonomials, monomial_one_right_eq_X_pow] using h
  have hb : Function.Surjective (Finsupp.linearCombination R (basisMonomials R)) := by
    rw [← Module.Basis.coe_repr_symm]
    exact (basisMonomials R).repr.symm.surjective
  let f : (ι × ℕ →₀ R) →ₗ[R] (ι →₀ R[X]) :=
    Finsupp.mapRange.linearMap (Finsupp.linearCombination R (basisMonomials R))
      ∘ₗ (Finsupp.curryLinearEquiv R).toLinearMap
  have hf : Function.Surjective f :=
    (Finsupp.mapRange_surjective (α := ι) _ (map_zero _) hb).comp
      (Finsupp.curryLinearEquiv R).surjective
  rw [← Finsupp.range_linearCombination (R := R[X]) (v := g),
    ← Finsupp.range_linearCombination (R := R)
      (v := fun p : ι × ℕ => basisMonomials R p.2 • g p.1),
    Finsupp.linearCombination_smul (R := R) (S := R[X]) (v := g)
      (w := (basisMonomials R : ℕ → R[X]))]
  apply SetLike.ext
  intro x
  change (∃ q : ι →₀ R[X], Finsupp.linearCombination R[X] g q = x) ↔
    ∃ p : ι × ℕ →₀ R, Finsupp.linearCombination R[X] g (f p) = x
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨p, hp⟩ := hf q
    exact ⟨p, (congrArg (Finsupp.linearCombination R[X] g) hp).trans hq⟩
  · rintro ⟨p, hp⟩
    exact ⟨f p, hp⟩

end Polynomial
