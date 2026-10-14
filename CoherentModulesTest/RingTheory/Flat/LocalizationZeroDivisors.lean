/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.Localization
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Joint faithful flatness over a ring with zero divisors

The canonical localizations of `ZMod 6` away from three and four are jointly
faithfully flat, since `3 + 4 = 1`. Both generators are nonzero zero divisors
and nonunits. Neither localization has faithful scalar action, so neither is
faithfully flat: two annihilates the localization away from three, and three
annihilates the localization away from four.

The localizations are nontrivial, as witnessed by ring maps to `ZMod 2` and
`ZMod 3`. Their reciprocals satisfy the unit equations and the annihilator
values. These examples use the canonical localization carriers and scalar
actions throughout.

## References

Joint faithful flatness uses CoherentModules' principal-localization criterion
`Module.FaithfullyFlat.directSum_away_iff`. The component boundaries use
Mathlib's implication from faithful flatness to faithful scalar action,
`Algebra.smul_def`, and `IsLocalization.Away.mul_invSelf`. Nontriviality uses
Mathlib's `ZMod.castHom` and the universal property of localization away from
an element. This formalization builds on the localization and faithfully flat
algebra APIs of Mathlib and CoherentModules.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

namespace CoherentModulesTest.Flat.LocalizationZeroDivisors

private abbrev generator (i : Fin 2) : ZMod 6 := if i = 0 then 3 else 4
private abbrev A3 := Localization.Away (3 : ZMod 6)
private abbrev A4 := Localization.Away (4 : ZMod 6)
private abbrev invThree : A3 := IsLocalization.Away.invSelf (3 : ZMod 6)
private abbrev invFour : A4 := IsLocalization.Away.invSelf (4 : ZMod 6)

private theorem generators_span : Ideal.span (Set.range generator) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h3 : (3 : ZMod 6) ∈ Ideal.span (Set.range generator) :=
    Ideal.mem_span_range_self (f := generator) (x := (0 : Fin 2))
  have h4 : (4 : ZMod 6) ∈ Ideal.span (Set.range generator) :=
    Ideal.mem_span_range_self (f := generator) (x := (1 : Fin 2))
  have hone : (3 : ZMod 6) + 4 = 1 := by decide
  rw [← hone]
  exact (Ideal.span (Set.range generator)).add_mem h3 h4

private theorem two_smul_awayThree (z : A3) : (2 : ZMod 6) • z = 0 := by
  have h23 : (2 : ZMod 6) * 3 = 0 := by decide
  have hmap : algebraMap (ZMod 6) A3 2 = 0 := by
    calc
      algebraMap (ZMod 6) A3 2 =
          algebraMap (ZMod 6) A3 2 *
            (algebraMap (ZMod 6) A3 3 * invThree) := by
        rw [IsLocalization.Away.mul_invSelf, mul_one]
      _ = algebraMap (ZMod 6) A3 ((2 : ZMod 6) * 3) * invThree := by
        rw [← mul_assoc, ← map_mul]
      _ = 0 := by rw [h23, map_zero, zero_mul]
  rw [Algebra.smul_def, hmap, zero_mul]

private theorem three_smul_awayFour (z : A4) : (3 : ZMod 6) • z = 0 := by
  have h34 : (3 : ZMod 6) * 4 = 0 := by decide
  have hmap : algebraMap (ZMod 6) A4 3 = 0 := by
    calc
      algebraMap (ZMod 6) A4 3 =
          algebraMap (ZMod 6) A4 3 *
            (algebraMap (ZMod 6) A4 4 * invFour) := by
        rw [IsLocalization.Away.mul_invSelf, mul_one]
      _ = algebraMap (ZMod 6) A4 ((3 : ZMod 6) * 4) * invFour := by
        rw [← mul_assoc, ← map_mul]
      _ = 0 := by rw [h34, map_zero, zero_mul]
  rw [Algebra.smul_def, hmap, zero_mul]

private theorem awayThree_not_faithfullyFlat : ¬ Module.FaithfullyFlat (ZMod 6) A3 := by
  intro h
  let : Module.FaithfullyFlat (ZMod 6) A3 := h
  apply (by decide : (2 : ZMod 6) ≠ 0)
  apply FaithfulSMul.algebraMap_injective (ZMod 6) A3
  simpa only [map_zero, Algebra.smul_def, mul_one] using two_smul_awayThree (1 : A3)

private theorem awayFour_not_faithfullyFlat : ¬ Module.FaithfullyFlat (ZMod 6) A4 := by
  intro h
  let : Module.FaithfullyFlat (ZMod 6) A4 := h
  apply (by decide : (3 : ZMod 6) ≠ 0)
  apply FaithfulSMul.algebraMap_injective (ZMod 6) A4
  simpa only [map_zero, Algebra.smul_def, mul_one] using three_smul_awayFour (1 : A4)

private def awayThreeToTwo : A3 →+* ZMod 2 :=
  Localization.awayLift (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) (3 : ZMod 6) (by
    have h : ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2) (3 : ZMod 6) = 1 := by decide
    rw [h]
    exact isUnit_one)

private def awayFourToThree : A4 →+* ZMod 3 :=
  Localization.awayLift (ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3)) (4 : ZMod 6) (by
    have h : ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3) (4 : ZMod 6) = 1 := by decide
    rw [h]
    exact isUnit_one)

/-- Three and four in `ZMod 6` are nonzero nonunits with nonzero annihilators. -/
public theorem zmodSixGeneratorsZeroDivisors :
    (3 : ZMod 6) ≠ 0 ∧ (4 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ≠ 0 ∧
      (2 : ZMod 6) * 3 = 0 ∧ (3 : ZMod 6) * 4 = 0 ∧
      ¬ IsUnit (3 : ZMod 6) ∧ ¬ IsUnit (4 : ZMod 6) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact (ZMod.isUnit_iff_coprime 3 6).not.mpr (by decide)
  · exact (ZMod.isUnit_iff_coprime 4 6).not.mpr (by decide)

/-- The base ring and both canonical localizations are nontrivial. The component
witnesses are the localization maps to `ZMod 2` and `ZMod 3`. -/
public theorem zmodSixAwayThreeFourNontrivial :
    Nontrivial (ZMod 6) ∧ Nontrivial (Localization.Away (3 : ZMod 6)) ∧
      Nontrivial (Localization.Away (4 : ZMod 6)) := by
  refine ⟨ZMod.nontrivial_iff.mpr (by decide), ?_, ?_⟩
  · let : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
    exact awayThreeToTwo.domain_nontrivial
  · let : Nontrivial (ZMod 3) := ZMod.nontrivial_iff.mpr (by decide)
    exact awayFourToThree.domain_nontrivial

/-- The two canonical localizations over `ZMod 6` are flat and jointly faithfully
flat, although neither component is faithfully flat. The unit-ideal witness is
`3 + 4 = 1`, so this example does not require a domain. -/
public theorem zmodSixAwayThreeFourDirectSum :
    (∀ i : Fin 2, Module.Flat (ZMod 6)
      (Localization.Away (if i = 0 then (3 : ZMod 6) else 4))) ∧
      Module.FaithfullyFlat (ZMod 6)
        (⨁ i : Fin 2, Localization.Away (if i = 0 then (3 : ZMod 6) else 4)) ∧
      ¬ Module.FaithfullyFlat (ZMod 6) (Localization.Away (3 : ZMod 6)) ∧
      ¬ Module.FaithfullyFlat (ZMod 6) (Localization.Away (4 : ZMod 6)) := by
  refine ⟨fun i ↦ IsLocalization.flat _ (Submonoid.powers (generator i)),
    ?_, awayThree_not_faithfullyFlat, awayFour_not_faithfullyFlat⟩
  exact (Module.FaithfullyFlat.directSum_away_iff (ZMod 6) generator).mpr generators_span

/-- The reciprocals obey their unit equations and are killed by the indicated
nonzero coefficients in `ZMod 6`. -/
public theorem zmodSixReciprocalValues :
    (3 : ZMod 6) • IsLocalization.Away.invSelf
        (S := Localization.Away (3 : ZMod 6)) (3 : ZMod 6) = 1 ∧
      (4 : ZMod 6) • IsLocalization.Away.invSelf
        (S := Localization.Away (4 : ZMod 6)) (4 : ZMod 6) = 1 ∧
      (2 : ZMod 6) • IsLocalization.Away.invSelf
        (S := Localization.Away (3 : ZMod 6)) (3 : ZMod 6) = 0 ∧
      (3 : ZMod 6) • IsLocalization.Away.invSelf
        (S := Localization.Away (4 : ZMod 6)) (4 : ZMod 6) = 0 := by
  refine ⟨?_, ?_, two_smul_awayThree invThree, three_smul_awayFour invFour⟩
  · rw [Algebra.smul_def, IsLocalization.Away.mul_invSelf]
  · rw [Algebra.smul_def, IsLocalization.Away.mul_invSelf]

end CoherentModulesTest.Flat.LocalizationZeroDivisors
