/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.DirectSum
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Principal localizations and joint faithful flatness

The canonical localizations of the integers away from two and three are flat
and have faithful scalar action, but neither is faithfully flat. Their dependent
direct sum is faithfully flat: the two generators span the unit ideal, so every
proper ideal has a nontrivial quotient-tensor fiber in at least one component.
The detecting component may depend on the ideal.

Reciprocals of two and three give concrete scalar and direct-sum coordinate
identities. Tensor distribution and the quotient-tensor equivalence are also
evaluated on included elements. A lifted index type checks the same coordinate
values in an independent universe. The empty localization family is not
faithfully flat over the integers, but is faithfully flat over the zero ring.

## References

The constructions use Mathlib's canonical localizations and localization
flatness, `Ideal.exists_disjoint_powers_of_span_eq_top`,
`IsLocalization.map_algebraMap_ne_top_iff_disjoint`, and
`Ideal.qoutMapEquivTensorQout`. Joint faithful flatness uses
`Module.FaithfullyFlat.directSum_iff` from CoherentModules. Tensor values use
Mathlib's tensor-distribution and quotient-tensor characteristic lemmas. The
negative examples use Mathlib's ideal-smul criterion for faithful flatness.
-/

@[expose] public section

open scoped DirectSum TensorProduct

noncomputable section

namespace CoherentModulesTest.Flat.Localization

universe v

private abbrev generator (i : Fin 2) : ℤ := if i = 0 then 2 else 3
private abbrev M (i : Fin 2) := Localization.Away (generator i)
private abbrev A2 := Localization.Away (2 : ℤ)
private abbrev A3 := Localization.Away (3 : ℤ)
private abbrev I2 : Ideal ℤ := Ideal.span ({2} : Set ℤ)
private abbrev I3 : Ideal ℤ := Ideal.span ({3} : Set ℤ)

private abbrev invTwo : A2 := IsLocalization.Away.invSelf (2 : ℤ)
private abbrev invThree : A3 := IsLocalization.Away.invSelf (3 : ℤ)

/-- The identity on a component, from its canonical integer module to the
integer module supplied by its localization algebra. -/
private def componentIntEquiv (i : Fin 2) :=
  @AddEquiv.toIntLinearEquiv (M i) (M i)
    (inferInstance : AddCommGroup (M i))
    (inferInstance : CommRing (M i)).toAddCommGroup
    (AddCommGroup.toIntModule (M i))
    (@Algebra.toModule ℤ (M i) inferInstance
      (inferInstance : CommRing (M i)).toSemiring inferInstance)
    (AddEquiv.refl (M i))

/-- The analogous identity for an ideal quotient of the integers. -/
private def quotientIntEquiv (I : Ideal ℤ) :=
  @AddEquiv.toIntLinearEquiv (ℤ ⧸ I) (ℤ ⧸ I)
    (inferInstance : AddCommGroup (ℤ ⧸ I))
    (inferInstance : CommRing (ℤ ⧸ I)).toAddCommGroup
    (AddCommGroup.toIntModule (ℤ ⧸ I))
    (@Algebra.toModule ℤ (ℤ ⧸ I) inferInstance
      (inferInstance : CommRing (ℤ ⧸ I)).toSemiring inferInstance)
    (AddEquiv.refl (ℤ ⧸ I))

private theorem component_int_smul (i : Fin 2) (n : ℤ) (z : M i) :
    n • z = algebraMap ℤ (M i) n * z := by
  exact ((componentIntEquiv i).map_smul n z).trans (Algebra.smul_def n z)

private theorem component_flat (i : Fin 2) : Module.Flat ℤ (M i) := by
  -- The equal carriers have different integer-module dictionaries.
  exact (@Module.Flat.equiv_iff ℤ (M i) (M i) inferInstance
    (inferInstance : AddCommGroup (M i)).toAddCommMonoid
    (AddCommGroup.toIntModule (M i))
    (inferInstance : CommRing (M i)).toAddCommGroup.toAddCommMonoid
    (@Algebra.toModule ℤ (M i) inferInstance
      (inferInstance : CommRing (M i)).toSemiring inferInstance)
    (componentIntEquiv i)).mpr
      (IsLocalization.flat (M i) (Submonoid.powers (generator i)))

private theorem generators_span : Ideal.span (Set.range generator) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h2 : (2 : ℤ) ∈ Ideal.span (Set.range generator) :=
    Ideal.mem_span_range_self (f := generator) (x := (0 : Fin 2))
  have h3 : (3 : ℤ) ∈ Ideal.span (Set.range generator) :=
    Ideal.mem_span_range_self (f := generator) (x := (1 : Fin 2))
  have hone : (-1 : ℤ) * 2 + 1 * 3 = 1 := by decide
  rw [← hone]
  exact (Ideal.span (Set.range generator)).add_mem
    ((Ideal.span (Set.range generator)).mul_mem_left (-1) h2)
    ((Ideal.span (Set.range generator)).mul_mem_left 1 h3)

private theorem sum_faithfullyFlat : Module.FaithfullyFlat ℤ (⨁ i : Fin 2, M i) := by
  apply (Module.FaithfullyFlat.directSum_iff ℤ M).mpr
  refine ⟨component_flat, ?_⟩
  intro I hI
  obtain ⟨r, ⟨i, rfl⟩, hdisjoint⟩ :=
    Ideal.exists_disjoint_powers_of_span_eq_top
      (Set.range generator) generators_span I hI
  have hmap : I.map (algebraMap ℤ (M i)) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (Submonoid.powers (generator i)) (M i) I).mpr hdisjoint.symm
  have hquot : Nontrivial ((M i) ⧸ I.map (algebraMap ℤ (M i))) :=
    Ideal.Quotient.nontrivial_iff.mpr hmap
  have htensor : Nontrivial ((M i) ⊗[ℤ] (ℤ ⧸ I)) :=
    -- Keep both canonical-to-algebra module bridges explicit.
    (@TensorProduct.congr ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
      (M i) (ℤ ⧸ I) (M i) (ℤ ⧸ I)
      (inferInstance : AddCommGroup (M i)).toAddCommMonoid
      (inferInstance : AddCommGroup (ℤ ⧸ I)).toAddCommMonoid
      (inferInstance : CommRing (M i)).toAddCommGroup.toAddCommMonoid
      (inferInstance : CommRing (ℤ ⧸ I)).toAddCommGroup.toAddCommMonoid
      (AddCommGroup.toIntModule (M i)) (AddCommGroup.toIntModule (ℤ ⧸ I))
      (@Algebra.toModule ℤ (M i) inferInstance
        (inferInstance : CommRing (M i)).toSemiring inferInstance)
      (@Algebra.toModule ℤ (ℤ ⧸ I) inferInstance
        (inferInstance : CommRing (ℤ ⧸ I)).toSemiring inferInstance)
      (RingHom.id ℤ) inferInstance inferInstance
      (componentIntEquiv i) (quotientIntEquiv I)).toEquiv.nontrivial_congr.mpr
        ((Ideal.qoutMapEquivTensorQout (R := ℤ) (I := I) (M i)).toEquiv.nontrivial_congr.mp
          hquot)
  exact ⟨i, (TensorProduct.comm ℤ (ℤ ⧸ I) (M i)).toEquiv.nontrivial_congr.mpr
    htensor⟩

private theorem two_smul_invTwo : (2 : ℤ) • invTwo = (1 : A2) := by
  rw [component_int_smul 0, IsLocalization.Away.mul_invSelf]

private theorem three_smul_invThree : (3 : ℤ) • invThree = (1 : A3) := by
  rw [component_int_smul 1, IsLocalization.Away.mul_invSelf]

private theorem two_proper : I2 ≠ ⊤ :=
  (Ideal.ne_top_iff_one I2).mpr fun hone ↦
    (by decide : ¬ (2 : ℤ) ∣ 1) (Ideal.mem_span_singleton.mp hone)

private theorem three_proper : I3 ≠ ⊤ :=
  (Ideal.ne_top_iff_one I3).mpr fun hone ↦
    (by decide : ¬ (3 : ℤ) ∣ 1) (Ideal.mem_span_singleton.mp hone)

private theorem two_not_faithfullyFlat : ¬ Module.FaithfullyFlat ℤ A2 := by
  intro h
  have hsmul : I2 • (⊤ : Submodule ℤ A2) = ⊤ := by
    apply top_unique
    intro z _
    have hz : (2 : ℤ) • (invTwo * z) = z := by
      rw [component_int_smul 0, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
    rw [← hz]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 2)
      (Submodule.mem_top : invTwo * z ∈ (⊤ : Submodule ℤ A2))
  exact two_proper
    (((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top ℤ A2).mp h).2 I2 hsmul)

private theorem three_not_faithfullyFlat : ¬ Module.FaithfullyFlat ℤ A3 := by
  intro h
  have hsmul : I3 • (⊤ : Submodule ℤ A3) = ⊤ := by
    apply top_unique
    intro z _
    have hz : (3 : ℤ) • (invThree * z) = z := by
      rw [component_int_smul 1, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
    rw [← hz]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 3)
      (Submodule.mem_top : invThree * z ∈ (⊤ : Submodule ℤ A3))
  exact three_proper
    (((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top ℤ A3).mp h).2 I3 hsmul)

/-- The canonical localizations away from two and three are flat and jointly
faithfully flat over the integers, although neither component is faithfully flat. -/
public theorem integerAwayTwoThreeDirectSum :
    (∀ i : Fin 2, Module.Flat ℤ
      (Localization.Away (if i = 0 then (2 : ℤ) else 3))) ∧
      Module.FaithfullyFlat ℤ
        (⨁ i : Fin 2, Localization.Away (if i = 0 then (2 : ℤ) else 3)) ∧
      ¬ Module.FaithfullyFlat ℤ (Localization.Away (2 : ℤ)) ∧
      ¬ Module.FaithfullyFlat ℤ (Localization.Away (3 : ℤ)) := by
  exact ⟨component_flat, sum_faithfullyFlat,
    two_not_faithfullyFlat, three_not_faithfullyFlat⟩

/-- Each of the two integer localizations has faithful scalar action, despite
its failure to be faithfully flat. -/
public theorem integerAwayTwoThreeFaithfulAction :
    FaithfulSMul ℤ (Localization.Away (2 : ℤ)) ∧
      FaithfulSMul ℤ (Localization.Away (3 : ℤ)) := by
  constructor
  · refine ⟨fun {a b} h ↦ ?_⟩
    apply IsLocalization.injective A2
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by decide : (2 : ℤ) ≠ 0))
    have hone := h (1 : A2)
    have hmap : (algebraMap ℤ (M 0) : ℤ →+* A2) = algebraMap ℤ A2 :=
      Subsingleton.elim _ _
    simpa only [component_int_smul 0, mul_one, hmap] using hone
  · refine ⟨fun {a b} h ↦ ?_⟩
    apply IsLocalization.injective A3
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by decide : (3 : ℤ) ≠ 0))
    have hone := h (1 : A3)
    have hmap : (algebraMap ℤ (M 1) : ℤ →+* A3) = algebraMap ℤ A3 :=
      Subsingleton.elim _ _
    simpa only [component_int_smul 1, mul_one, hmap] using hone

/-- The canonical reciprocal values satisfy the expected integer scalar equations. -/
public theorem integerReciprocalValues :
    (2 : ℤ) • IsLocalization.Away.invSelf (S := Localization.Away (2 : ℤ))
        (2 : ℤ) = 1 ∧
      (3 : ℤ) • IsLocalization.Away.invSelf (S := Localization.Away (3 : ℤ))
        (3 : ℤ) = 1 := by
  exact ⟨two_smul_invTwo, three_smul_invThree⟩

private def reciprocalPair : ⨁ i : Fin 2, M i :=
  DirectSum.lof ℤ (Fin 2) M 0 invTwo + DirectSum.lof ℤ (Fin 2) M 1 invThree

example :
    DirectSum.component ℤ (Fin 2) M 0 reciprocalPair = invTwo ∧
      DirectSum.component ℤ (Fin 2) M 1 reciprocalPair = invThree := by
  constructor <;> simp [reciprocalPair, DirectSum.component.of]

example :
    TensorProduct.quotTensorEquivQuotSMul A3 I2
        ((1 : ℤ ⧸ I2) ⊗ₜ[ℤ] invThree) = Submodule.Quotient.mk invThree := by
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I2 invThree

example :
    TensorProduct.quotTensorEquivQuotSMul (⨁ i : Fin 2, M i) I2
        ((1 : ℤ ⧸ I2) ⊗ₜ[ℤ] reciprocalPair) =
      Submodule.Quotient.mk reciprocalPair := by
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I2 reciprocalPair

example :
    TensorProduct.directSumRight ℤ ℤ (ℤ ⧸ I2) M
        ((1 : ℤ ⧸ I2) ⊗ₜ[ℤ] DirectSum.lof ℤ (Fin 2) M 1 invThree) =
      DirectSum.lof ℤ (Fin 2) (fun i ↦ (ℤ ⧸ I2) ⊗[ℤ] M i) 1
        ((1 : ℤ ⧸ I2) ⊗ₜ[ℤ] invThree) := by
  have h := TensorProduct.directSumRight_tmul_lof ℤ ℤ
    (M₁' := ℤ ⧸ I2) (M₂ := M)
    (1 : ℤ ⧸ I2) (1 : Fin 2) (show M 1 from invThree)
  exact h

private abbrev liftedM (i : ULift.{v} (Fin 2)) := M i.down

example :
    DirectSum.component ℤ (ULift.{v} (Fin 2)) liftedM ⟨0⟩
        (DirectSum.lof ℤ (ULift.{v} (Fin 2)) liftedM ⟨0⟩ invTwo +
          DirectSum.lof ℤ (ULift.{v} (Fin 2)) liftedM ⟨1⟩ invThree) = invTwo ∧
      DirectSum.component ℤ (ULift.{v} (Fin 2)) liftedM ⟨1⟩
        (DirectSum.lof ℤ (ULift.{v} (Fin 2)) liftedM ⟨0⟩ invTwo +
          DirectSum.lof ℤ (ULift.{v} (Fin 2)) liftedM ⟨1⟩ invThree) = invThree := by
  classical
  constructor <;> simp [DirectSum.component.of]

/-- The empty family of canonical integer localizations is flat but not
faithfully flat. -/
public theorem integerEmptyLocalizationDirectSum :
    Module.Flat ℤ (⨁ i : Fin 0, Localization.Away (Fin.elim0 i : ℤ)) ∧
      ¬ Module.FaithfullyFlat ℤ
        (⨁ i : Fin 0, Localization.Away (Fin.elim0 i : ℤ)) := by
  constructor
  · apply Module.Flat.directSum_iff.mpr
    intro i
    exact Fin.elim0 i
  · intro h
    obtain ⟨i, _⟩ :=
      ((Module.FaithfullyFlat.directSum_iff ℤ
        (fun i : Fin 0 ↦ Localization.Away (Fin.elim0 i : ℤ))).mp h).2 ⊥ bot_ne_top
    exact Fin.elim0 i

/-- Over the zero ring, the empty family of canonical localizations is
faithfully flat because there are no proper ideals. -/
public theorem trivialScalarEmptyLocalizationDirectSum :
    Module.FaithfullyFlat (ZMod 1)
      (⨁ i : Fin 0, Localization.Away (Fin.elim0 i : ZMod 1)) := by
  let : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  apply (Module.FaithfullyFlat.directSum_iff (ZMod 1)
    (fun i : Fin 0 ↦ Localization.Away (Fin.elim0 i : ZMod 1))).mpr
  refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
  intro I hI
  exact (hI (Subsingleton.elim I ⊤)).elim

end CoherentModulesTest.Flat.Localization
