/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Left-regular elements in left Artinian rings

A left-regular element of a left Artinian ring is a unit. The ring may be
noncommutative or zero. Artinianity concerns the original left regular module;
no Artinianity of the opposite ring is assumed.

Mathlib's `IsArtinianRing.isUnit_iff_isLeftRegular` instead applies to semirings
whose opposite is left Artinian. The two sets of hypotheses are incomparable.
The implication from units to left-regular elements is already provided by
`IsUnit.isRegular`.

## References

The mathematical argument uses the Fitting decomposition formalized in
`Mathlib.RingTheory.Artinian.Module` and the Hopkins–Levitzki theorem formalized
by Junyan Xu in `Mathlib.RingTheory.HopkinsLevitzki`.
-/

@[expose] public section

universe u

/-- A left-regular element of a left Artinian ring is a unit.
Artinianity is required only for the original left regular module, not for the
opposite ring. No commutativity or nontriviality assumption is needed. -/
theorem IsLeftRegular.isUnit_of_isArtinianRing
    {A : Type u} [Ring A] [IsArtinianRing A] {a : A} (ha : IsLeftRegular a) :
    IsUnit a := by
  -- Right multiplication is linear on the original left regular module.
  let f : Module.End A A := LinearMap.mulRight A a
  have hf (n : ℕ) (x : A) : (f ^ n) x = x * a ^ n := by
    simp only [f, LinearMap.pow_mulRight, LinearMap.mulRight_apply]
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  -- A positive exponent is needed to recover a unit from a unit power.
  let n := k + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero k
  have hcompl := hk n (Nat.le_succ k)
  have hone : (1 : A) ∈ LinearMap.ker (f ^ n) ⊔ LinearMap.range (f ^ n) := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨b, hb, d, hd, hbd⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hd
  have hbn : b * a ^ n = 0 := by
    simpa only [LinearMap.mem_ker, hf] using hb
  have hbc : b + c * a ^ n = 1 := by
    simpa only [hf] using hbd
  -- Left and right multiplication give two kernel/range decompositions of a.
  have hab : a * b ∈ LinearMap.ker (f ^ n) := by
    change (f ^ n) (a * b) = 0
    rw [hf, mul_assoc, hbn, mul_zero]
  have hba : b * a ∈ LinearMap.ker (f ^ n) := by
    change (f ^ n) (b * a) = 0
    rw [hf, mul_assoc, ← pow_succ', pow_succ, ← mul_assoc, hbn, zero_mul]
  have hac : (a * c) * a ^ n ∈ LinearMap.range (f ^ n) :=
    LinearMap.mem_range.mpr ⟨a * c, hf n _⟩
  have hca : (c * a) * a ^ n ∈ LinearMap.range (f ^ n) :=
    LinearMap.mem_range.mpr ⟨c * a, hf n _⟩
  have hleft : a * b + (a * c) * a ^ n = a := by
    simpa only [mul_add, mul_assoc, mul_one] using congrArg (a * ·) hbc
  have hright : b * a + (c * a) * a ^ n = a := by
    simpa only [add_mul, one_mul, mul_assoc, ← pow_succ, ← pow_succ'] using
      congrArg (· * a) hbc
  -- Uniqueness of the complementary decomposition forces a and b to commute.
  have hdiff : a * b - b * a = (c * a) * a ^ n - (a * c) * a ^ n := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using hleft.trans hright.symm
  have hmem : a * b - b * a ∈ LinearMap.ker (f ^ n) ⊓ LinearMap.range (f ^ n) :=
    ⟨Submodule.sub_mem _ hab hba, by rw [hdiff]; exact Submodule.sub_mem _ hca hac⟩
  have hcomm : Commute a b := by
    apply sub_eq_zero.mp
    simpa only [hcompl.inf_eq_bot, Submodule.mem_bot] using hmem
  have hb0 : b = 0 := (ha.pow n) <|
    ((hcomm.pow_left n).eq.trans hbn).trans (mul_zero (a ^ n)).symm
  have hunit : IsUnit (a ^ n) :=
    IsUnit.of_mul_eq_one_right c (by simpa only [hb0, zero_add] using hbc)
  exact (isUnit_pow_iff hn).mp hunit
