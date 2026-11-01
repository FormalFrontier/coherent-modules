/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Extension of products and powers of left ideals

For a unital homomorphism of semirings, extension preserves a product of left
ideals whenever the extension of the first factor is two-sided. In particular,
extension preserves every power of an ideal whose extension is two-sided.
Neither semiring needs to be commutative, and the homomorphism need not be
surjective.

## References

The product argument follows the span proof of Mathlib's `Ideal.map_mul` in
`Mathlib.RingTheory.Ideal.Maps`, using `Ideal.span_mul_span` from
`Mathlib.RingTheory.Ideal.Operations` with its first-factor two-sidedness
hypothesis. Powers use Mathlib's two-sided-ideal power instance.
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal

variable {A : Type u} {B : Type v} [Semiring A] [Semiring B]

/-- Extension preserves a product of left ideals if the extension of the first
factor is two-sided. No two-sidedness assumption is needed on either source
ideal or on the extension of the second factor. -/
theorem map_mul_of_isTwoSided (f : A →+* B) (I J : Ideal A)
    [(map f I).IsTwoSided] : map f (I * J) = map f I * map f J := by
  have hmul : span ((I : Set A) * (J : Set A)) = I * J := by
    refine le_antisymm (span_le.2 ?_) (mul_le.2 ?_)
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact mul_mem_mul ha hb
    · intro a ha b hb
      exact subset_span ⟨a, ha, b, hb, rfl⟩
  have : (span (f '' (I : Set A))).IsTwoSided :=
    inferInstanceAs (map f I).IsTwoSided
  calc
    map f (I * J) = span (f '' ((I : Set A) * (J : Set A))) := by
      rw [← hmul, map_span]
    _ = span ((f '' (I : Set A)) * (f '' (J : Set A))) := by
      rw [Set.image_mul]
    _ = map f I * map f J := (span_mul_span _ _).symm

/-- Extension preserves all powers of a left ideal whose extension is two-sided,
including the zeroth power. -/
theorem map_pow_of_isTwoSided (f : A →+* B) (I : Ideal A)
    [(map f I).IsTwoSided] (n : ℕ) : map f (I ^ n) = map f I ^ n := by
  induction n with
  | zero => simp only [Submodule.pow_zero, one_eq_top, map_top]
  | succ n ih =>
    have : (map f (I ^ n)).IsTwoSided := by
      rw [ih]
      infer_instance
    rw [Submodule.pow_succ, map_mul_of_isTwoSided, ih, Submodule.pow_succ]

end Ideal
