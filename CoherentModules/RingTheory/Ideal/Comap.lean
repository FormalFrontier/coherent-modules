/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import CoherentModules.RingTheory.Ideal.Maps

/-!
# Inverse-image bounds for ideals

Inverse image under a semiring homomorphism is submultiplicative for ideal products and
powers. If `J ^ m = 0` and `(RingHom.ker f) ^ n = 0`, then
`(J.comap f) ^ (m * n) = 0`. In particular, inverse images of nilpotent ideals are nilpotent
when the kernel is nilpotent. These bounds include zero exponents.

## References

The product and power inclusions generalize Mathlib's `Ideal.le_comap_mul` and
`Ideal.le_comap_pow` to arbitrary semirings. The commutative-semiring statements retain
their original homomorphism-class generality, arbitrary ideals, and all natural exponents.
-/

@[expose] public section

universe u v w

namespace Ideal

/-- The product of inverse images is contained in the inverse image of the product,
generalizing Mathlib's `Ideal.le_comap_mul`. -/
theorem comap_mul_comap_le
    {R : Type u} {S : Type v} {F : Type w}
    [Semiring R] [Semiring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) {I J : Ideal S} :
    I.comap f * J.comap f ≤ (I * J).comap f := by
  refine Ideal.mul_le.mpr fun x hx y hy => ?_
  apply Ideal.mem_comap.mpr
  rw [map_mul]
  exact Ideal.mul_mem_mul (Ideal.mem_comap.mp hx) (Ideal.mem_comap.mp hy)

/-- A power of an inverse image is contained in the inverse image of the corresponding power,
generalizing Mathlib's `Ideal.le_comap_pow`. -/
theorem pow_comap_le_comap_pow
    {R : Type u} {S : Type v} {F : Type w}
    [Semiring R] [Semiring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (J : Ideal S) (n : ℕ) :
    J.comap f ^ n ≤ (J ^ n).comap f := by
  induction n with
  | zero =>
      simpa only [Submodule.pow_zero, one_eq_top, comap_top] using
        (le_rfl : (⊤ : Ideal R) ≤ ⊤)
  | succ n ih =>
      simp only [Submodule.pow_succ]
      exact (mul_mono ih le_rfl).trans (comap_mul_comap_le f)

/-- Nilpotence bounds for an ideal and the kernel give a bound for the ideal's inverse image. -/
theorem pow_comap_eq_zero_of_ker_pow_eq_zero
    {R : Type u} {S : Type v} {F : Type w}
    [Semiring R] [Semiring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (J : Ideal S) {m n : ℕ}
    (hJ : J ^ m = 0) (hK : RingHom.ker f ^ n = 0) :
    J.comap f ^ (m * n) = 0 := by
  have hle : J.comap f ^ m ≤ RingHom.ker f := by
    calc
      J.comap f ^ m ≤ (J ^ m).comap f := pow_comap_le_comap_pow f J m
      _ = RingHom.ker f := by rw [hJ, Ideal.zero_eq_bot, RingHom.ker_eq_comap_bot]
  have hpow : J.comap f ^ (m * n) = (J.comap f ^ m) ^ n := by
    open scoped Pointwise in
      by_cases hn : n = 0
      · subst n
        simp only [Nat.mul_zero, Submodule.pow_zero]
      by_cases hm : m = 0
      · subst m
        simp only [Nat.zero_mul, Submodule.pow_zero, Ideal.one_eq_top, Ideal.top_pow]
      apply Submodule.toAddSubmonoid_injective
      rw [Submodule.pow_toAddSubmonoid (J.comap f) (Nat.mul_ne_zero hm hn),
        Submodule.pow_toAddSubmonoid (J.comap f ^ m) hn,
        Submodule.pow_toAddSubmonoid (J.comap f) hm]
      exact pow_mul (J.comap f).toAddSubmonoid m n
  apply le_antisymm _ bot_le
  calc
    J.comap f ^ (m * n) = (J.comap f ^ m) ^ n := hpow
    _ ≤ RingHom.ker f ^ n := Ideal.pow_right_mono hle n
    _ = 0 := hK

/-- An inverse image is nilpotent when the ideal and the homomorphism's kernel are nilpotent. -/
theorem isNilpotent_comap
    {R : Type u} {S : Type v} {F : Type w}
    [Semiring R] [Semiring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) {J : Ideal S}
    (hJ : IsNilpotent J) (hK : IsNilpotent (RingHom.ker f)) :
    IsNilpotent (J.comap f) := by
  obtain ⟨m, hm⟩ := hJ
  obtain ⟨n, hn⟩ := hK
  exact ⟨m * n, pow_comap_eq_zero_of_ker_pow_eq_zero f J hm hn⟩

/-- Mathlib's `Ideal.le_comap_mul` statement, with its commutative-semiring hypotheses. -/
private theorem comap_mul_comap_le_commSemiring
    {R : Type u} {S : Type v} {F : Type w}
    [CommSemiring R] [CommSemiring S] [FunLike F R S] [rc : RingHomClass F R S]
    (f : F) {K L : Ideal S} :
    comap f K * comap f L ≤ comap f (K * L) := by
  exact comap_mul_comap_le f (I := K) (J := L)

/-- Mathlib's `Ideal.le_comap_pow` statement, with its commutative-semiring hypotheses. -/
private theorem pow_comap_le_comap_pow_commSemiring
    {R : Type u} {S : Type v} {F : Type w}
    [CommSemiring R] [CommSemiring S] [FunLike F R S] [rc : RingHomClass F R S]
    (f : F) {K : Ideal S} (n : ℕ) :
    K.comap f ^ n ≤ (K ^ n).comap f := by
  exact pow_comap_le_comap_pow f K n

end Ideal
