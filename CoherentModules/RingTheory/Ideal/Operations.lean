/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Relative generation bounds for ideal powers

A relative bound by the action of an ideal persists along every ideal power.
Consequently, a globally nilpotent ideal cannot enlarge relative generation.
The scalar semiring need not be commutative, and no finite-generation hypothesis
is imposed on the semimodule or its submodules.

The power bound extracts the ideal-action iteration used in
`Submodule.fg_of_finite_quotient_smul` in
`CoherentModules.RingTheory.Ideal.AdicKrull`.

## References

* The ideal/submodule product, power and scalar-action APIs in
  `Mathlib.Algebra.Algebra.Operations` and `Mathlib.RingTheory.Ideal.Operations`.
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
