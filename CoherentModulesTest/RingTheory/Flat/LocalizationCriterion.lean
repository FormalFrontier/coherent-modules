/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.Localization
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Clients of the principal-localization family criterion

The unit-ideal criterion constructs faithfully flat direct sums for complementary
denominators `r` and `1 - r` over any commutative ring, and for a countably infinite
family whose zeroth denominator is one. The latter sum contains a nonzero included
unit whenever the base ring is nontrivial.

The empty localization family is not faithfully flat over a nontrivial ring, but
is faithfully flat over a subsingleton ring. A complementary family indexed by
`ULift (Fin 2)` also checks an index universe independent of the ring universe.
Its included reciprocal is evaluated by the coordinate projection and satisfies
the localization inverse equation.

## References

These examples use the CoherentModules criterion
`Module.FaithfullyFlat.directSum_away_iff`, together with Mathlib's ideal-span,
direct-sum coordinate and principal-localization APIs. In particular, the value
calculations use `DirectSum.component.lof_self`, `IsLocalization.atOne` and
`IsLocalization.Away.mul_invSelf`, rather than the implementations of those maps.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

namespace CoherentModulesTest.Flat.LocalizationCriterion

universe u v

variable (R : Type u) [CommRing R]

/- The constructor-case families have the same pointwise values as the conditional
families: the natural-number family is one at zero and zero at successors; the
`Fin 2` family is `r` at zero and `1 - r` at one. Constructor cases also make the
zeroth localization carrier reduce to `Localization.Away 1` or `Localization.Away r`. -/
private def complementaryDenominators (r : R) (i : Fin 2) : R :=
  Fin.cases (motive := fun _ ↦ R) r (fun _ ↦ 1 - r) i

/-- The complementary denominators `r` and `1 - r` give a faithfully flat sum of
principal localizations, since their sum is one. -/
theorem complementaryAwayDirectSum (r : R) :
    Module.FaithfullyFlat R
      (⨁ i : Fin 2,
        Localization.Away (Fin.cases (motive := fun _ ↦ R) r (fun _ ↦ 1 - r) i)) := by
  apply (Module.FaithfullyFlat.directSum_away_iff R (complementaryDenominators R r)).2
  apply (Ideal.eq_top_iff_one _).2
  have hr : r ∈ Ideal.span (Set.range (complementaryDenominators R r)) := by
    simpa [complementaryDenominators] using
      (Ideal.mem_span_range_self (f := complementaryDenominators R r) (x := (0 : Fin 2)))
  have hsub : 1 - r ∈ Ideal.span (Set.range (complementaryDenominators R r)) := by
    simpa only [complementaryDenominators, Fin.cases_succ] using
      (Ideal.mem_span_range_self (f := complementaryDenominators R r) (x := (0 : Fin 1).succ))
  simpa only [sub_add_cancel] using (Ideal.span _).add_mem hsub hr

private def unitFirstDenominators (n : ℕ) : R :=
  Nat.casesOn (motive := fun _ ↦ R) n (1 : R) (fun _ ↦ 0)

/-- A countably infinite family with denominator one at zero gives a faithfully
flat sum, even though every other denominator is zero. -/
theorem countableUnitAwayDirectSum :
    Module.FaithfullyFlat R
      (⨁ n : ℕ,
        Localization.Away (Nat.casesOn (motive := fun _ ↦ R) n (1 : R) (fun _ ↦ 0))) := by
  apply (Module.FaithfullyFlat.directSum_away_iff R (unitFirstDenominators R)).2
  apply (Ideal.eq_top_iff_one _).2
  simpa [unitFirstDenominators] using
    (Ideal.mem_span_range_self (f := unitFirstDenominators R) (x := 0))

/-- The zeroth included unit in the countable localization sum is nonzero over
any nontrivial base ring. -/
theorem countableUnitAwayDirectSum_one_ne_zero [Nontrivial R] :
    DirectSum.lof R ℕ
      (fun n ↦ Localization.Away (Nat.casesOn (motive := fun _ ↦ R) n (1 : R) (fun _ ↦ 0))) 0
      (1 : Localization.Away (1 : R)) ≠ 0 := by
  intro h
  have hcomponent : (1 : Localization.Away (1 : R)) = 0 := by
    simpa only [DirectSum.component.lof_self, map_zero] using
      congrArg
        (DirectSum.component R ℕ
          (fun n ↦ Localization.Away (Nat.casesOn (motive := fun _ ↦ R) n (1 : R) (fun _ ↦ 0))) 0) h
  have hbase := congrArg (IsLocalization.atOne R (Localization.Away (1 : R))).symm hcomponent
  exact one_ne_zero (by simpa only [map_one, map_zero] using hbase)

/-- The empty localization family fails the unit-ideal criterion over every
nontrivial commutative ring. -/
theorem emptyAwayDirectSum_not_faithfullyFlat [Nontrivial R] :
    ¬ Module.FaithfullyFlat R
      (⨁ i : Fin 0, Localization.Away (Fin.elim0 i : R)) := by
  intro h
  have hspan :=
    (Module.FaithfullyFlat.directSum_away_iff R (fun i : Fin 0 ↦ (Fin.elim0 i : R))).1 h
  have hrange : Set.range (fun i : Fin 0 ↦ (Fin.elim0 i : R)) = ∅ := by
    ext x
    simp
  rw [hrange, Ideal.span_empty] at hspan
  exact bot_ne_top hspan

/-- Over a subsingleton commutative ring, the empty family generates the unit
ideal and its direct sum of principal localizations is faithfully flat. -/
theorem emptyAwayDirectSum_of_subsingleton [Subsingleton R] :
    Module.FaithfullyFlat R
      (⨁ i : Fin 0, Localization.Away (Fin.elim0 i : R)) := by
  apply
    (Module.FaithfullyFlat.directSum_away_iff R (fun i : Fin 0 ↦ (Fin.elim0 i : R))).2
  apply (Ideal.eq_top_iff_one _).2
  rw [Subsingleton.elim (1 : R) 0]
  exact (Ideal.span _).zero_mem

private def liftedComplementaryDenominators (r : R) (i : ULift.{v} (Fin 2)) : R :=
  complementaryDenominators R r i.down

/-- Complementary denominators still give a faithfully flat sum when the index
universe is independent of the ring universe. -/
theorem liftedComplementaryAwayDirectSum (r : R) :
    Module.FaithfullyFlat R
      (⨁ i : ULift.{v} (Fin 2),
        Localization.Away (Fin.cases (motive := fun _ ↦ R) r (fun _ ↦ 1 - r) i.down)) := by
  apply
    (Module.FaithfullyFlat.directSum_away_iff R
      (liftedComplementaryDenominators.{u, v} R r)).2
  apply (Ideal.eq_top_iff_one _).2
  have hr : r ∈ Ideal.span (Set.range (liftedComplementaryDenominators.{u, v} R r)) := by
    simpa [liftedComplementaryDenominators, complementaryDenominators] using
      (Ideal.mem_span_range_self (f := liftedComplementaryDenominators.{u, v} R r)
        (x := (ULift.up (0 : Fin 2) : ULift.{v} (Fin 2))))
  have hsub : 1 - r ∈ Ideal.span (Set.range (liftedComplementaryDenominators.{u, v} R r)) := by
    simpa only [liftedComplementaryDenominators, complementaryDenominators, Fin.cases_succ] using
      (Ideal.mem_span_range_self (f := liftedComplementaryDenominators.{u, v} R r)
        (x := (ULift.up (0 : Fin 1).succ : ULift.{v} (Fin 2))))
  simpa only [sub_add_cancel] using (Ideal.span _).add_mem hsub hr

/-- The reciprocal included in the lifted zeroth coordinate is recovered by the
coordinate map. The scalar equation uses the canonical indexed localization;
`Fin.cases_zero` identifies its denominator with `r`, and `Algebra.smul_def`
identifies the equation with being an inverse to the image of `r`. -/
theorem liftedComplementaryReciprocal_coordinate (r : R) :
    r • DirectSum.component R (ULift.{v} (Fin 2))
      (fun i ↦
        Localization.Away (Fin.cases (motive := fun _ ↦ R) r (fun _ ↦ 1 - r) i.down)) (ULift.up 0)
      (DirectSum.lof R _ _ (ULift.up 0)
        (IsLocalization.Away.invSelf
          (S := Localization.Away
            (Fin.cases (motive := fun _ ↦ R) r (fun _ ↦ 1 - r)
              (ULift.up (0 : Fin 2) : ULift.{v} (Fin 2)).down))
          (Fin.cases (motive := fun _ ↦ R) r (fun _ ↦ 1 - r)
            (ULift.up (0 : Fin 2) : ULift.{v} (Fin 2)).down))) = 1 := by
  rw [DirectSum.component.lof_self]
  change r • IsLocalization.Away.invSelf (S := Localization.Away r) r = 1
  rw [Algebra.smul_def]
  exact IsLocalization.Away.mul_invSelf (S := Localization.Away r) r

end CoherentModulesTest.Flat.LocalizationCriterion
