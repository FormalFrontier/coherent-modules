/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Nilpotent ideal sums and relative generation

The join of two globally nilpotent left ideals is globally nilpotent, with a
vanishing-power bound given by the sum of the two exponents minus one. More
generally, a power of a join is bounded by the two-sided closures of the
corresponding powers. The scalar semiring need not be commutative.

A relative bound by the action of an ideal persists along every ideal power.
Consequently, a globally nilpotent ideal cannot enlarge relative generation.
No finite-generation hypothesis is imposed on the semimodule or its submodules.

The power bound extracts the ideal-action iteration used in
`Submodule.fg_of_finite_quotient_smul` in
`CoherentModules.RingTheory.Ideal.AdicKrull`.

## References

* The ideal/submodule product, power and scalar-action APIs in
  `Mathlib.Algebra.Algebra.Operations` and `Mathlib.RingTheory.Ideal.Operations`,
  including the commutative containment `Ideal.sup_pow_add_le_pow_sup_pow`.
* The relative ideal-power iteration in
  `CoherentModules.RingTheory.Ideal.AdicKrull`.
-/

@[expose] public section

universe uR uM

open scoped Pointwise

namespace Submodule

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- A relative generation bound by an ideal action persists along every ideal power. -/
theorem le_sup_pow_smul_of_le_sup_smul
    {I : Ideal R} {N P : Submodule R M}
    (h : P ≤ N ⊔ I • P) (n : ℕ) :
    P ≤ N ⊔ (I ^ n) • P := by
  induction n with
  | zero =>
    rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact le_sup_right
  | succ n ih =>
    -- Acting on the original bound keeps the right-successor order `I ^ n * I`.
    calc
      P ≤ N ⊔ (I ^ n) • P := ih
      _ ≤ N ⊔ (I ^ n) • (N ⊔ I • P) :=
        sup_le_sup le_rfl (Submodule.smul_mono le_rfl h)
      _ = N ⊔ ((I ^ n) • N ⊔ (I ^ n) • (I • P)) := by
        rw [Submodule.smul_sup]
      _ = (N ⊔ (I ^ n) • N) ⊔ (I ^ n) • (I • P) :=
        (sup_assoc _ _ _).symm
      _ ≤ N ⊔ (I ^ n) • (I • P) :=
        sup_le_sup (sup_le le_rfl Submodule.smul_le_right) le_rfl
      _ = N ⊔ (I ^ (n + 1)) • P := by
        rw [← Submodule.mul_smul, ← Submodule.pow_succ]

/-- Relative generation by a globally nilpotent ideal gives containment in the
comparison submodule. No finite-generation hypothesis is required. -/
theorem le_of_le_sup_smul_of_isNilpotent
    {I : Ideal R} {N P : Submodule R M}
    (hI : IsNilpotent I) (h : P ≤ N ⊔ I • P) :
    P ≤ N := by
  obtain ⟨n, hn⟩ := hI
  simpa only [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] using
    le_sup_pow_smul_of_le_sup_smul h n

end Submodule

namespace Ideal

section Semiring

variable {R : Type uR} [Semiring R]

private theorem mul_top_pow (I : Ideal R) (k : ℕ) :
    (I * ⊤) ^ k = I ^ k * ⊤ := by
  induction k with
  | zero => simp only [Submodule.pow_zero, one_eq_top, top_mul]
  | succ k ih =>
    simp only [Submodule.pow_succ, ih, Ideal.mul_assoc, top_mul]

private theorem sup_pow_add_sub_one_le_of_isTwoSided
    (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] (m n : ℕ) :
    (I ⊔ J) ^ (m + n - 1) ≤ I ^ m ⊔ J ^ n := by
  induction m generalizing n with
  | zero =>
    rw [Submodule.pow_zero, one_eq_top, top_sup_eq]
    exact le_top
  | succ m ihm =>
    induction n with
    | zero =>
      rw [Submodule.pow_zero, one_eq_top, sup_top_eq]
      exact le_top
    | succ n ihn =>
      have hI : (I ⊔ J) ^ (m + n) ≤ I ^ m ⊔ J ^ (n + 1) := by
        simpa only [Nat.add_succ, Nat.succ_sub_one] using ihm (n + 1)
      have hJ : (I ⊔ J) ^ (m + n) ≤ I ^ (m + 1) ⊔ J ^ n := by
        simpa only [Nat.succ_add, Nat.succ_sub_one] using ihn
      have hmulI : (I ⊔ J) ^ (m + n) * I ≤ I ^ (m + 1) ⊔ J ^ (n + 1) := by
        calc
          (I ⊔ J) ^ (m + n) * I ≤ (I ^ m ⊔ J ^ (n + 1)) * I :=
            mul_mono_left hI
          _ = I ^ (m + 1) ⊔ J ^ (n + 1) * I := by
            rw [sup_mul, ← Submodule.pow_succ]
          _ ≤ I ^ (m + 1) ⊔ J ^ (n + 1) := sup_le_sup le_rfl mul_le_left
      have hmulJ : (I ⊔ J) ^ (m + n) * J ≤ I ^ (m + 1) ⊔ J ^ (n + 1) := by
        calc
          (I ⊔ J) ^ (m + n) * J ≤ (I ^ (m + 1) ⊔ J ^ n) * J :=
            mul_mono_left hJ
          _ = I ^ (m + 1) * J ⊔ J ^ (n + 1) := by
            rw [sup_mul, ← Submodule.pow_succ]
          _ ≤ I ^ (m + 1) ⊔ J ^ (n + 1) := sup_le_sup mul_le_left le_rfl
      simpa only [Nat.succ_add, Nat.add_succ, Nat.succ_sub_one,
        Submodule.pow_succ, mul_sup] using sup_le hmulI hmulJ

/-- A power of the join of two left ideals is bounded by the two-sided closures
of the corresponding powers. No commutativity or two-sidedness of the input
ideals is required. -/
theorem sup_pow_add_sub_one_le (I J : Ideal R) (m n : ℕ) :
    (I ⊔ J) ^ (m + n - 1) ≤ I ^ m * ⊤ ⊔ J ^ n * ⊤ := by
  have h : ∀ K : Ideal R, K ≤ K * ⊤ := by
    intro K x hx
    simpa only [mul_one] using
      (mul_mem_mul hx (show (1 : R) ∈ (⊤ : Ideal R) from Submodule.mem_top))
  calc
    (I ⊔ J) ^ (m + n - 1) ≤ (I * ⊤ ⊔ J * ⊤) ^ (m + n - 1) :=
      pow_right_mono (sup_le_sup (h I) (h J)) _
    _ ≤ (I * ⊤) ^ m ⊔ (J * ⊤) ^ n :=
      sup_pow_add_sub_one_le_of_isTwoSided (I * ⊤) (J * ⊤) m n
    _ = I ^ m * ⊤ ⊔ J ^ n * ⊤ := by rw [mul_top_pow, mul_top_pow]

/-- If powers of two left ideals vanish, the power of their join with exponent
the sum of the two exponents minus one vanishes. This includes zero exponents
and the zero semiring. -/
theorem sup_pow_add_sub_one_eq_zero (I J : Ideal R) {m n : ℕ}
    (hI : I ^ m = 0) (hJ : J ^ n = 0) :
    (I ⊔ J) ^ (m + n - 1) = 0 := by
  apply le_antisymm ?_ bot_le
  simpa only [hI, hJ, zero_eq_bot, bot_mul, sup_idem] using
    sup_pow_add_sub_one_le I J m n

/-- The join of globally nilpotent left ideals is globally nilpotent over any
semiring, without a commutation or two-sidedness hypothesis. -/
theorem isNilpotent_sup {I J : Ideal R}
    (hI : IsNilpotent I) (hJ : IsNilpotent J) : IsNilpotent (I ⊔ J) := by
  obtain ⟨m, hm⟩ := hI
  obtain ⟨n, hn⟩ := hJ
  exact ⟨m + n - 1, sup_pow_add_sub_one_eq_zero I J hm hn⟩

end Semiring

section CommSemiring

variable {R : Type uR} [CommSemiring R]

private theorem sup_pow_add_le_pow_sup_pow_from_top_bound
    {I J : Ideal R} {n m : ℕ} : (I ⊔ J) ^ (n + m) ≤ I ^ n ⊔ J ^ m := by
  calc
    (I ⊔ J) ^ (n + m) ≤ (I ⊔ J) ^ (n + m - 1) :=
      pow_le_pow_right (Nat.sub_le _ _)
    _ ≤ I ^ n ⊔ J ^ m := by
      simpa only [mul_top] using sup_pow_add_sub_one_le I J n m

end CommSemiring

end Ideal
