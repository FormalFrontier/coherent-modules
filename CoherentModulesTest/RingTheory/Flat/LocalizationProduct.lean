/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModulesTest.RingTheory.Flat.Localization
public import CoherentModulesTest.RingTheory.Flat.LocalizationZeroDivisors
public import CoherentModules.RingTheory.Flat.Localization
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.FinCases

/-!
# Finite products of canonical principal localizations

The integer denominators two and three, and the zero-divisor denominators three
and four in `ZMod 6`, give concrete faithfully flat product modules. Faithful
flatness is transported from the corresponding direct sums by Mathlib's finite
sum/function linear equivalence. The product rings retain their canonical
algebra maps and diagonal scalar actions; individual components need not be
faithfully flat.

The reciprocal tuples are evaluated under scalar multiplication, coordinate
projection, and the finite sum/function equivalence. Each denominator-image
tuple multiplies the same reciprocal tuple to one. Empty products over the
integers and the zero ring give opposite faithful-flatness boundaries. A lifted
two-element index checks the constructions in an independent index universe.
A countable product of two-by-two matrix algebras over `ZMod 2` supplies a
noncommutative product-algebra example: entry projection is a surjective linear
map to the base field, while two matrix-unit tuples fail to commute.

## References

Faithful flatness uses the principal-localization direct-sum criterion
`Module.FaithfullyFlat.directSum_away_iff` and the concrete direct-sum clients.
Transport and values use `DirectSum.linearEquivFunOnFintype`,
`DirectSum.linearEquivFunOnFintype_lof`,
`Module.FaithfullyFlat.of_linearEquiv`, and
`IsLocalization.Away.mul_invSelf`. Integer scalar compatibility uses
`AddEquiv.toIntLinearEquiv` to compare the canonical integer-module and
algebra-module dictionaries explicitly. The matrix example uses
`Matrix.entryLinearMap`, `LinearMap.proj`, stock flatness of vector spaces, and
`Module.FaithfullyFlat.of_surjective`.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

namespace CoherentModulesTest.Flat.LocalizationProduct

universe v

/-- The integer denominators two and three, in that order. -/
def integerDenominator (i : Fin 2) : ℤ := if i = 0 then 2 else 3

/-- The canonical localization in each integer coordinate. -/
abbrev integerAway (i : Fin 2) := Localization.Away (integerDenominator i)

/-- The dependent product, with its canonical ring and integer action. -/
abbrev IntegerProduct := ∀ i : Fin 2, integerAway i

/-- The tuple of canonical reciprocals, not an included single coordinate. -/
def integerReciprocal : IntegerProduct := fun i ↦
  IsLocalization.Away.invSelf (S := integerAway i) (integerDenominator i)

/-- The coordinatewise images of the respective denominators. -/
def integerDenominatorImage : IntegerProduct := fun i ↦
  algebraMap ℤ (integerAway i) (integerDenominator i)

/-- Each coordinate of the integer reciprocal tuple is the canonical reciprocal. -/
@[simp]
theorem integerReciprocal_apply (i : Fin 2) :
    integerReciprocal i =
      IsLocalization.Away.invSelf (S := integerAway i) (integerDenominator i) := rfl

/-- Each coordinate of the integer denominator-image tuple is its localization image. -/
@[simp]
theorem integerDenominatorImage_apply (i : Fin 2) :
    integerDenominatorImage i = algebraMap ℤ (integerAway i) (integerDenominator i) := rfl

/-- The finite product is faithfully flat, although neither component is. -/
theorem integerProduct_faithfullyFlat :
    Module.FaithfullyFlat ℤ IntegerProduct ∧
      ¬ Module.FaithfullyFlat ℤ (Localization.Away (2 : ℤ)) ∧
      ¬ Module.FaithfullyFlat ℤ (Localization.Away (3 : ℤ)) := by
  classical
  let : Fintype (Fin 2) := Fintype.ofFinite (Fin 2)
  have hsum : Module.FaithfullyFlat ℤ (⨁ i : Fin 2, integerAway i) :=
    Localization.integerAwayTwoThreeDirectSum.2.1
  let := hsum
  let e := @AddEquiv.toIntLinearEquiv
    (⨁ i : Fin 2, integerAway i) IntegerProduct
    (inferInstance : AddCommGroup (⨁ i : Fin 2, integerAway i))
    (inferInstance : AddCommGroup IntegerProduct) inferInstance inferInstance
    { (DirectSum.linearEquivFunOnFintype ℤ (Fin 2) integerAway).toEquiv with
      map_add' := by
        intro x y
        funext i
        rfl }
  exact ⟨Module.FaithfullyFlat.of_linearEquiv ℤ _ e.symm,
    Localization.integerAwayTwoThreeDirectSum.2.2⟩

/-- The diagonal integer map has the canonical localization value in every
coordinate. Uniqueness of integer ring homomorphisms avoids identifying algebra
instance dictionaries by definitional equality. -/
theorem integerProduct_algebraMap (n : ℤ) (i : Fin 2) :
    algebraMap ℤ IntegerProduct n i = algebraMap ℤ (integerAway i) n := by
  change ((Pi.evalRingHom integerAway i).comp (algebraMap ℤ IntegerProduct)) n =
    algebraMap ℤ (integerAway i) n
  exact RingHom.congr_fun (Subsingleton.elim _ _) n

/-- The denominator tuple and the reciprocal tuple are multiplicative inverses
in the canonical product ring. -/
theorem integerDenominatorImage_mul_reciprocal :
    integerDenominatorImage * integerReciprocal = 1 := by
  funext i
  rw [Pi.mul_apply, integerDenominatorImage_apply, integerReciprocal_apply]
  exact IsLocalization.Away.mul_invSelf (S := integerAway i) (integerDenominator i)

/-- Integer scalar multiplication of this tuple agrees with the diagonal
algebra action, without replacing the canonical integer module. -/
theorem integerReciprocal_smul (n : ℤ) :
    n • integerReciprocal = algebraMap ℤ IntegerProduct n * integerReciprocal := by
  let e := @AddEquiv.toIntLinearEquiv IntegerProduct IntegerProduct
    (inferInstance : AddCommGroup IntegerProduct)
    (inferInstance : CommRing IntegerProduct).toAddCommGroup
    (AddCommGroup.toIntModule IntegerProduct)
    (@Algebra.toModule ℤ IntegerProduct inferInstance
      (inferInstance : CommRing IntegerProduct).toSemiring inferInstance)
    (AddEquiv.refl IntegerProduct)
  exact (e.map_smul n integerReciprocal).trans (Algebra.smul_def n integerReciprocal)

/-- The two projections recover different reciprocals and their scalar unit
values. -/
theorem integerReciprocal_coordinates :
    integerReciprocal 0 =
      IsLocalization.Away.invSelf (S := Localization.Away (2 : ℤ)) (2 : ℤ) ∧
    integerReciprocal 1 =
      IsLocalization.Away.invSelf (S := Localization.Away (3 : ℤ)) (3 : ℤ) ∧
    ((2 : ℤ) • integerReciprocal) 0 = 1 ∧
    ((3 : ℤ) • integerReciprocal) 1 = 1 := by
  refine ⟨integerReciprocal_apply 0, integerReciprocal_apply 1, ?_, ?_⟩
  · exact Localization.integerReciprocalValues.1
  · exact Localization.integerReciprocalValues.2

/-- Six times the same reciprocal tuple has coordinates three and two. -/
theorem integerReciprocal_six_smul :
    ((6 : ℤ) • integerReciprocal) 0 = algebraMap ℤ (integerAway 0) 3 ∧
      ((6 : ℤ) • integerReciprocal) 1 = algebraMap ℤ (integerAway 1) 2 := by
  have h2 : algebraMap ℤ (integerAway 0) 2 * integerReciprocal 0 = 1 := by
    have h := integerReciprocal_coordinates.2.2.1
    rw [integerReciprocal_smul, Pi.mul_apply, integerProduct_algebraMap] at h
    exact h
  have h3 : algebraMap ℤ (integerAway 1) 3 * integerReciprocal 1 = 1 := by
    have h := integerReciprocal_coordinates.2.2.2
    rw [integerReciprocal_smul, Pi.mul_apply, integerProduct_algebraMap] at h
    exact h
  constructor
  · rw [integerReciprocal_smul, Pi.mul_apply, integerProduct_algebraMap]
    rw [show (6 : ℤ) = 3 * 2 by decide, map_mul, mul_assoc, h2, mul_one]
  · rw [integerReciprocal_smul, Pi.mul_apply, integerProduct_algebraMap]
    rw [show (6 : ℤ) = 2 * 3 by decide, map_mul, mul_assoc, h3, mul_one]

/-- This reciprocal tuple is nonzero in the canonical localization product. -/
theorem integerReciprocal_ne_zero : integerReciprocal ≠ 0 := by
  intro h
  have hcoord : integerReciprocal 0 = 0 := congrFun h 0
  have hone : (1 : integerAway 0) = 0 := by
    calc
      1 = integerDenominatorImage 0 * integerReciprocal 0 :=
        (congrFun integerDenominatorImage_mul_reciprocal 0).symm
      _ = 0 := by rw [hcoord, mul_zero]
  have hinj := IsLocalization.injective (integerAway 0)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (by decide : integerDenominator 0 ≠ 0))
  exact (by decide : (1 : ℤ) ≠ 0)
    (hinj (by simpa only [map_one, map_zero] using hone))

/-- In particular, the integer product is a nonzero ring. -/
theorem integerProduct_nontrivial : Nontrivial IntegerProduct :=
  ⟨⟨integerReciprocal, 0, integerReciprocal_ne_zero⟩⟩

/-- The finite sum/function equivalence sends the sum of the two included
reciprocals to the same reciprocal tuple used in the multiplication tests. -/
theorem integerSumEquiv_reciprocal :
    DirectSum.linearEquivFunOnFintype ℤ (Fin 2) integerAway
      (DirectSum.lof ℤ (Fin 2) integerAway 0 (integerReciprocal 0) +
        DirectSum.lof ℤ (Fin 2) integerAway 1 (integerReciprocal 1)) =
      integerReciprocal := by
  classical
  rw [map_add, DirectSum.linearEquivFunOnFintype_lof,
    DirectSum.linearEquivFunOnFintype_lof]
  funext i
  fin_cases i <;> simp

/-- A single included reciprocal becomes a single supported tuple, not a
diagonal tuple. -/
theorem integerSumEquiv_single_coordinates :
    (DirectSum.linearEquivFunOnFintype ℤ (Fin 2) integerAway
      (DirectSum.lof ℤ (Fin 2) integerAway 0 (integerReciprocal 0))) 0 =
        integerReciprocal 0 ∧
    (DirectSum.linearEquivFunOnFintype ℤ (Fin 2) integerAway
      (DirectSum.lof ℤ (Fin 2) integerAway 0 (integerReciprocal 0))) 1 = 0 := by
  classical
  constructor
  · rw [DirectSum.linearEquivFunOnFintype_lof, Pi.single_eq_same]
  · rw [DirectSum.linearEquivFunOnFintype_lof,
      Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- The empty integer product of canonical localizations. -/
abbrev IntegerEmptyProduct :=
  ∀ i : Fin 0, Localization.Away (Fin.elim0 i : ℤ)

/-- The empty product of canonical localizations over the zero ring. -/
abbrev ZeroEmptyProduct :=
  ∀ i : Fin 0, Localization.Away (Fin.elim0 i : ZMod 1)

/-- The empty integer product is flat but not faithfully flat. -/
theorem integerEmptyProduct_flat_not_faithfullyFlat :
    Module.Flat ℤ IntegerEmptyProduct ∧
      ¬ Module.FaithfullyFlat ℤ IntegerEmptyProduct := by
  classical
  let : Fintype (Fin 0) := Fintype.ofFinite (Fin 0)
  let e := DirectSum.linearEquivFunOnFintype ℤ (Fin 0)
    (fun i ↦ Localization.Away (Fin.elim0 i : ℤ))
  constructor
  · let := Localization.integerEmptyLocalizationDirectSum.1
    exact Module.Flat.of_linearEquiv e.symm
  · intro h
    let := h
    exact Localization.integerEmptyLocalizationDirectSum.2
      (Module.FaithfullyFlat.of_linearEquiv ℤ _ e)

/-- The same empty product is faithfully flat over the zero ring. -/
theorem zeroEmptyProduct_faithfullyFlat :
    Module.FaithfullyFlat (ZMod 1) ZeroEmptyProduct := by
  classical
  let : Fintype (Fin 0) := Fintype.ofFinite (Fin 0)
  let := Localization.trivialScalarEmptyLocalizationDirectSum
  exact Module.FaithfullyFlat.of_linearEquiv (ZMod 1) _
    (DirectSum.linearEquivFunOnFintype (ZMod 1) (Fin 0)
      (fun i ↦ Localization.Away (Fin.elim0 i : ZMod 1))).symm

/-- Empty products have zero values for their units, scalar images,
and scalar actions; there is no coordinate to inspect. -/
theorem emptyProduct_values :
    (0 : IntegerEmptyProduct) = 1 ∧
      algebraMap ℤ IntegerEmptyProduct 7 = 0 ∧
      (7 : ℤ) • (1 : IntegerEmptyProduct) = 0 ∧
      (0 : ZeroEmptyProduct) = 1 ∧
      algebraMap (ZMod 1) ZeroEmptyProduct 1 = 0 := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Three and four are nonzero zero-divisor denominators in `ZMod 6`. -/
def zmodSixDenominator (i : Fin 2) : ZMod 6 := if i = 0 then 3 else 4

/-- The canonical localization in each `ZMod 6` coordinate. -/
abbrev zmodSixAway (i : Fin 2) := Localization.Away (zmodSixDenominator i)

/-- The canonical product algebra over `ZMod 6`. -/
abbrev ZModSixProduct := ∀ i : Fin 2, zmodSixAway i

/-- The tuple of the two canonical reciprocals over `ZMod 6`. -/
def zmodSixReciprocal : ZModSixProduct := fun i ↦
  IsLocalization.Away.invSelf (S := zmodSixAway i) (zmodSixDenominator i)

/-- Images of the respective zero-divisor denominators. -/
def zmodSixDenominatorImage : ZModSixProduct := fun i ↦
  algebraMap (ZMod 6) (zmodSixAway i) (zmodSixDenominator i)

/-- Each coordinate of the `ZMod 6` reciprocal tuple is the canonical reciprocal. -/
@[simp]
theorem zmodSixReciprocal_apply (i : Fin 2) :
    zmodSixReciprocal i =
      IsLocalization.Away.invSelf (S := zmodSixAway i) (zmodSixDenominator i) := rfl

/-- Each coordinate of the `ZMod 6` denominator-image tuple is its localization image. -/
@[simp]
theorem zmodSixDenominatorImage_apply (i : Fin 2) :
    zmodSixDenominatorImage i =
      algebraMap (ZMod 6) (zmodSixAway i) (zmodSixDenominator i) := rfl

/-- The unit-ideal identity `3 + 4 = 1` gives a faithfully flat product even
though neither localization is faithfully flat. -/
theorem zmodSixProduct_faithfullyFlat :
    Module.FaithfullyFlat (ZMod 6) ZModSixProduct ∧
      ¬ Module.FaithfullyFlat (ZMod 6) (Localization.Away (3 : ZMod 6)) ∧
      ¬ Module.FaithfullyFlat (ZMod 6) (Localization.Away (4 : ZMod 6)) := by
  classical
  let : Fintype (Fin 2) := Fintype.ofFinite (Fin 2)
  have hspan : Ideal.span (Set.range zmodSixDenominator) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).2
    have h3 : (3 : ZMod 6) ∈ Ideal.span (Set.range zmodSixDenominator) :=
      Ideal.mem_span_range_self (f := zmodSixDenominator) (x := (0 : Fin 2))
    have h4 : (4 : ZMod 6) ∈ Ideal.span (Set.range zmodSixDenominator) :=
      Ideal.mem_span_range_self (f := zmodSixDenominator) (x := (1 : Fin 2))
    rw [← show (3 : ZMod 6) + 4 = 1 by decide]
    exact (Ideal.span _).add_mem h3 h4
  let : Module.FaithfullyFlat (ZMod 6) (⨁ i : Fin 2, zmodSixAway i) :=
    (Module.FaithfullyFlat.directSum_away_iff (ZMod 6) zmodSixDenominator).2 hspan
  exact ⟨Module.FaithfullyFlat.of_linearEquiv (ZMod 6) _
    (DirectSum.linearEquivFunOnFintype (ZMod 6) (Fin 2) zmodSixAway).symm,
    LocalizationZeroDivisors.zmodSixAwayThreeFourDirectSum.2.2⟩

/-- The canonical product algebra map is coordinatewise the localization map. -/
theorem zmodSixProduct_algebraMap (r : ZMod 6) (i : Fin 2) :
    algebraMap (ZMod 6) ZModSixProduct r i =
      algebraMap (ZMod 6) (zmodSixAway i) r := by
  rfl

/-- The same reciprocal tuple inverts the denominator-image tuple, including
for these zero-divisor denominators. -/
theorem zmodSixDenominatorImage_mul_reciprocal :
    zmodSixDenominatorImage * zmodSixReciprocal = 1 := by
  funext i
  rw [Pi.mul_apply, zmodSixDenominatorImage_apply, zmodSixReciprocal_apply]
  exact IsLocalization.Away.mul_invSelf (S := zmodSixAway i) (zmodSixDenominator i)

/-- Nonzero coefficients act as complementary coordinate projections on the
reciprocal tuple. In particular, the action is not replaced by a field action. -/
theorem zmodSixReciprocal_scalar_values :
    (3 : ZMod 6) • zmodSixReciprocal = Pi.single 0 (1 : zmodSixAway 0) ∧
      (4 : ZMod 6) • zmodSixReciprocal = Pi.single 1 (1 : zmodSixAway 1) := by
  classical
  have h := LocalizationZeroDivisors.zmodSixReciprocalValues
  have hfour : (4 : ZMod 6) •
      IsLocalization.Away.invSelf (S := Localization.Away (3 : ZMod 6))
        (3 : ZMod 6) = 0 := by
    rw [show (4 : ZMod 6) = 2 * 2 by decide, mul_smul, h.2.2.1, smul_zero]
  constructor
  · funext i
    rw [Pi.smul_apply, zmodSixReciprocal_apply]
    fin_cases i
    · exact h.1
    · exact h.2.2.2
  · funext i
    rw [Pi.smul_apply, zmodSixReciprocal_apply]
    fin_cases i
    · exact hfour
    · exact h.2.1

/-- The two scalar pieces sum back to the original reciprocal tuple. -/
theorem zmodSixReciprocal_scalar_sum :
    (3 : ZMod 6) • zmodSixReciprocal + (4 : ZMod 6) • zmodSixReciprocal =
      zmodSixReciprocal := by
  rw [← add_smul, show (3 : ZMod 6) + 4 = 1 by decide, one_smul]

/-- The reciprocal product tuple is nonzero, using the nontrivial canonical
localization rather than cancellation in the zero-divisor base ring. -/
theorem zmodSixReciprocal_ne_zero : zmodSixReciprocal ≠ 0 := by
  let : Nontrivial (zmodSixAway 0) :=
    LocalizationZeroDivisors.zmodSixAwayThreeFourNontrivial.2.1
  intro h
  have hcoord : zmodSixReciprocal 0 = 0 := congrFun h 0
  have hunit : (3 : ZMod 6) • zmodSixReciprocal 0 = (1 : zmodSixAway 0) :=
    LocalizationZeroDivisors.zmodSixReciprocalValues.1
  rw [hcoord, smul_zero] at hunit
  exact (zero_ne_one : (0 : zmodSixAway 0) ≠ 1) hunit

/-- The finite sum/function equivalence has the same reciprocal value over
the zero-divisor base. -/
theorem zmodSixSumEquiv_reciprocal :
    DirectSum.linearEquivFunOnFintype (ZMod 6) (Fin 2) zmodSixAway
      (DirectSum.lof (ZMod 6) (Fin 2) zmodSixAway 0 (zmodSixReciprocal 0) +
        DirectSum.lof (ZMod 6) (Fin 2) zmodSixAway 1 (zmodSixReciprocal 1)) =
      zmodSixReciprocal := by
  classical
  rw [map_add, DirectSum.linearEquivFunOnFintype_lof,
    DirectSum.linearEquivFunOnFintype_lof]
  funext i
  fin_cases i <;> simp

/-- The same integer family with an independently lifted index universe. -/
def liftedIntegerDenominator (i : ULift.{v} (Fin 2)) : ℤ := integerDenominator i.down

/-- Canonical localizations indexed in the lifted universe. -/
abbrev liftedIntegerAway (i : ULift.{v} (Fin 2)) :=
  Localization.Away (liftedIntegerDenominator i)

/-- The lifted dependent product. -/
abbrev LiftedIntegerProduct := ∀ i : ULift.{v} (Fin 2), liftedIntegerAway i

/-- The lifted tuple of canonical reciprocals. -/
def liftedIntegerReciprocal : LiftedIntegerProduct.{v} := fun i ↦
  IsLocalization.Away.invSelf (S := liftedIntegerAway i) (liftedIntegerDenominator i)

/-- The corresponding lifted denominator-image tuple. -/
def liftedIntegerDenominatorImage : LiftedIntegerProduct.{v} := fun i ↦
  algebraMap ℤ (liftedIntegerAway i) (liftedIntegerDenominator i)

/-- Each lifted coordinate of the reciprocal tuple is the canonical reciprocal. -/
@[simp]
theorem liftedIntegerReciprocal_apply (i : ULift.{v} (Fin 2)) :
    liftedIntegerReciprocal i =
      IsLocalization.Away.invSelf (S := liftedIntegerAway i) (liftedIntegerDenominator i) := rfl

/-- Each lifted coordinate of the denominator-image tuple is its localization image. -/
@[simp]
theorem liftedIntegerDenominatorImage_apply (i : ULift.{v} (Fin 2)) :
    liftedIntegerDenominatorImage i =
      algebraMap ℤ (liftedIntegerAway i) (liftedIntegerDenominator i) := rfl

/-- Reindexing the integer direct sum and then using the finite
sum/function equivalence proves faithful flatness in the lifted universe. -/
theorem liftedIntegerProduct_faithfullyFlat :
    Module.FaithfullyFlat ℤ LiftedIntegerProduct.{v} := by
  classical
  let : Fintype (ULift.{v} (Fin 2)) := Fintype.ofFinite (ULift.{v} (Fin 2))
  let e := @AddEquiv.toIntLinearEquiv
    (⨁ i : Fin 2, integerAway i)
    (⨁ i : ULift.{v} (Fin 2), liftedIntegerAway i)
    (inferInstance : AddCommGroup (⨁ i : Fin 2, integerAway i))
    (inferInstance : AddCommGroup (⨁ i : ULift.{v} (Fin 2), liftedIntegerAway i))
    inferInstance inferInstance
    { (DFinsupp.domLCongr (R := ℤ) (M := integerAway)
        (Equiv.ulift.symm : Fin 2 ≃ ULift.{v} (Fin 2))).toEquiv with
      map_add' := by
        intro x y
        ext i
        rfl }
  let : Module.FaithfullyFlat ℤ (⨁ i : Fin 2, integerAway i) :=
    Localization.integerAwayTwoThreeDirectSum.2.1
  let : Module.FaithfullyFlat ℤ (⨁ i : ULift.{v} (Fin 2), liftedIntegerAway i) :=
    Module.FaithfullyFlat.of_linearEquiv ℤ _ e.symm
  let f := @AddEquiv.toIntLinearEquiv
    (⨁ i : ULift.{v} (Fin 2), liftedIntegerAway i) LiftedIntegerProduct.{v}
    (inferInstance : AddCommGroup (⨁ i : ULift.{v} (Fin 2), liftedIntegerAway i))
    (inferInstance : AddCommGroup LiftedIntegerProduct.{v}) inferInstance inferInstance
    { (DirectSum.linearEquivFunOnFintype ℤ (ULift.{v} (Fin 2))
        liftedIntegerAway).toEquiv with
      map_add' := by
        intro x y
        funext i
        rfl }
  exact Module.FaithfullyFlat.of_linearEquiv ℤ _ f.symm

/-- The lifted product still uses the canonical diagonal integer map. -/
theorem liftedIntegerProduct_algebraMap (n : ℤ) (i : ULift.{v} (Fin 2)) :
    algebraMap ℤ LiftedIntegerProduct.{v} n i =
      algebraMap ℤ (liftedIntegerAway i) n := by
  change ((Pi.evalRingHom liftedIntegerAway i).comp
    (algebraMap ℤ LiftedIntegerProduct.{v})) n = algebraMap ℤ (liftedIntegerAway i) n
  exact RingHom.congr_fun (Subsingleton.elim _ _) n

/-- The inverse equation uses the same lifted reciprocal tuple as the
coordinate and equivalence values. -/
theorem liftedIntegerDenominatorImage_mul_reciprocal :
    liftedIntegerDenominatorImage.{v} * liftedIntegerReciprocal.{v} = 1 := by
  funext i
  rw [Pi.mul_apply, liftedIntegerDenominatorImage_apply, liftedIntegerReciprocal_apply]
  exact IsLocalization.Away.mul_invSelf (S := liftedIntegerAway i)
    (liftedIntegerDenominator i)

/-- The lifted coordinates retain the distinct reciprocal and scalar values. -/
theorem liftedIntegerReciprocal_coordinates :
    liftedIntegerReciprocal (ULift.up (0 : Fin 2) : ULift.{v} (Fin 2)) =
      IsLocalization.Away.invSelf (S := Localization.Away (2 : ℤ)) (2 : ℤ) ∧
    liftedIntegerReciprocal (ULift.up (1 : Fin 2) : ULift.{v} (Fin 2)) =
      IsLocalization.Away.invSelf (S := Localization.Away (3 : ℤ)) (3 : ℤ) ∧
    ((2 : ℤ) • liftedIntegerReciprocal) (ULift.up (0 : Fin 2) : ULift.{v} (Fin 2)) = 1 ∧
    ((3 : ℤ) • liftedIntegerReciprocal) (ULift.up (1 : Fin 2) : ULift.{v} (Fin 2)) = 1 := by
  refine ⟨liftedIntegerReciprocal_apply _, liftedIntegerReciprocal_apply _, ?_, ?_⟩
  · exact Localization.integerReciprocalValues.1
  · exact Localization.integerReciprocalValues.2

/-- The lifted finite sum/function equivalence evaluates to the lifted
reciprocal tuple itself. -/
theorem liftedIntegerSumEquiv_reciprocal :
    DirectSum.linearEquivFunOnFintype ℤ (ULift.{v} (Fin 2)) liftedIntegerAway
      (DirectSum.lof ℤ (ULift.{v} (Fin 2)) liftedIntegerAway ⟨0⟩
        (liftedIntegerReciprocal ⟨0⟩) +
      DirectSum.lof ℤ (ULift.{v} (Fin 2)) liftedIntegerAway ⟨1⟩
        (liftedIntegerReciprocal ⟨1⟩)) = liftedIntegerReciprocal.{v} := by
  classical
  rw [map_add, DirectSum.linearEquivFunOnFintype_lof,
    DirectSum.linearEquivFunOnFintype_lof]
  funext i
  rcases i with ⟨i⟩
  fin_cases i <;> simp

/-- The full two-by-two matrix ring over the two-element field, with matrix
multiplication rather than pointwise multiplication of entries. -/
abbrev BinaryMatrix := Matrix (Fin 2) (Fin 2) (ZMod 2)

/-- A countable product of these canonical noncommutative algebras. -/
abbrev MatrixSequence := ℕ → BinaryMatrix

/-- Coordinate zero followed by entry `(0, 0)`, as a linear map. Entry
projection is not asserted to be a ring homomorphism. -/
def matrixSequenceEntry : MatrixSequence →ₗ[ZMod 2] ZMod 2 :=
  (Matrix.entryLinearMap (ZMod 2) (ZMod 2) (0 : Fin 2) (0 : Fin 2)).comp
    (LinearMap.proj 0 : MatrixSequence →ₗ[ZMod 2] BinaryMatrix)

/-- A constant tuple whose only possibly nonzero matrix entry is `(0, 0)`. -/
def matrixSequenceEntryWitness (a : ZMod 2) : MatrixSequence :=
  fun _ ↦ Matrix.single 0 0 a

/-- The composed linear projection has its coordinate-entry value. -/
theorem matrixSequenceEntry_apply (z : MatrixSequence) :
    matrixSequenceEntry z = z 0 0 0 := by
  rfl

/-- Every base-field value is attained by the displayed constant tuple. -/
theorem matrixSequenceEntry_witness (a : ZMod 2) :
    matrixSequenceEntry (matrixSequenceEntryWitness a) = a := by
  simp [matrixSequenceEntry, matrixSequenceEntryWitness]

/-- The countable product of noncommutative matrix algebras is
faithfully flat over `ZMod 2`, using vector-space flatness and a surjective
linear projection onto the faithfully flat regular module. -/
theorem matrixSequence_faithfullyFlat :
    Module.FaithfullyFlat (ZMod 2) MatrixSequence := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Module.Free (ZMod 2) MatrixSequence :=
    Module.Free.of_divisionRing (ZMod 2) MatrixSequence
  let : Module.Flat (ZMod 2) MatrixSequence :=
    Module.Flat.of_free (R := ZMod 2) (M := MatrixSequence)
  apply Module.FaithfullyFlat.of_surjective matrixSequenceEntry
  intro a
  exact ⟨matrixSequenceEntryWitness a, matrixSequenceEntry_witness a⟩

/-- The constant tuple of the matrix unit `E₀₁`. -/
def matrixSequenceE01 : MatrixSequence := fun _ ↦ Matrix.single 0 1 1

/-- The constant tuple of the matrix unit `E₁₀`. -/
def matrixSequenceE10 : MatrixSequence := fun _ ↦ Matrix.single 1 0 1

/-- Multiplication is noncommutative: the two ordered products
have respective `(0, 0)` entries one and zero, in coordinate zero. -/
theorem matrixSequence_mul_values :
    (matrixSequenceE01 * matrixSequenceE10) 0 0 0 = 1 ∧
      (matrixSequenceE10 * matrixSequenceE01) 0 0 0 = 0 := by
  constructor <;> decide

/-- The displayed matrix-unit tuples do not commute in the product ring. -/
theorem matrixSequence_mul_ne :
    matrixSequenceE01 * matrixSequenceE10 ≠ matrixSequenceE10 * matrixSequenceE01 := by
  intro h
  have hentry := congrArg (fun z : MatrixSequence ↦ z 0 0 0) h
  rw [matrixSequence_mul_values.1, matrixSequence_mul_values.2] at hentry
  exact (by decide : (1 : ZMod 2) ≠ 0) hentry

end CoherentModulesTest.Flat.LocalizationProduct
