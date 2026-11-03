/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.End.StableKernelRange
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Local endomorphism rings of indecomposable finite-length modules

For a module of finite length over an arbitrary ring, categorical
indecomposability implies that every endomorphism is nilpotent or a unit and
that the endomorphism ring is local. The scalar ring need not be commutative.

`CategoryTheory.Indecomposable (ModuleCat.of R M)` includes the assertion that
the module is not zero. No separate nontriviality hypothesis is needed.
Finite length is expressed by the stock `IsFiniteLength R M`; over ring
scalars it is equivalent to Noetherianity and Artinianity of the module.

## References

Robert Wisbauer, *Foundations of Module and Ring Theory: A Handbook for Study
and Research*, Gordon and Breach, 1991, §32.4(3)(iii) and its proof, gives the
classical finite-length indecomposable local-endomorphism theorem and the
nilpotent-or-invertible alternative, using Fitting's lemma in §31.13;
[author's text](https://www.math.uni-duesseldorf.de/~wisbauer/book.pdf).
These are ring-module results. The Lean proof below uses the explicit one-step
semiring/additive-group Fitting API in `StableKernelRange`, but the local-ring
conclusion here retains ring scalars; the reference is not claimed to give the
broader semiring decomposition.

The Lean proofs reuse Mathlib's APIs. The categorical predicate is
`CategoryTheory.Indecomposable` from
`Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`.
The submodule criterion uses the complement sum equivalence in
`Mathlib.LinearAlgebra.Projection` and
`ModuleCat.biprodIsoProd` in `Mathlib.Algebra.Category.ModuleCat.Biproducts`,
together with the characterizations of zero
module objects and bottom submodules by subsingleton carriers.
-/

@[expose] public section

universe uR uM

namespace Submodule

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- In an indecomposable module, complementary submodules cannot both be nonzero. -/
theorem eq_bot_or_eq_bot_of_isCompl_of_indecomposable
    (hM : CategoryTheory.Indecomposable (ModuleCat.of R M))
    (P Q : Submodule R M) (hPQ : IsCompl P Q) : P = ⊥ ∨ Q = ⊥ := by
  have h := hM.2 (ModuleCat.of R P) (ModuleCat.of R Q)
    ((P.prodEquivOfIsCompl Q hPQ).symm.toModuleIso ≪≫
      (ModuleCat.biprodIsoProd (ModuleCat.of R P) (ModuleCat.of R Q)).symm)
  exact h.imp
    (fun hP => Submodule.subsingleton_iff_eq_bot.mp
      (ModuleCat.isZero_of_iff_subsingleton.mp hP))
    (fun hQ => Submodule.subsingleton_iff_eq_bot.mp
      (ModuleCat.isZero_of_iff_subsingleton.mp hQ))

end Submodule

namespace Module.End

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- Every endomorphism of an indecomposable finite-length module is nilpotent or a unit.
This is the classical ring-module alternative in the proof of Wisbauer,
*Foundations of Module and Ring Theory*, §32.4(3)(iii), via Fitting's lemma
(§31.13). The Lean proof uses the explicit-one-step semiring/additive-group
Fitting generalization, but this theorem retains ring scalars and nonzeroness
through the categorical indecomposable predicate. -/
theorem isNilpotent_or_isUnit_of_indecomposable_of_isFiniteLength
    (hM : CategoryTheory.Indecomposable (ModuleCat.of R M))
    (hLength : IsFiniteLength R M) (f : Module.End R M) :
    IsNilpotent f ∨ IsUnit f := by
  obtain ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hLength
  let := hNoetherian
  let := hArtinian
  obtain ⟨n, hK, hI⟩ := exists_stable_ker_range f
  -- Move to a positive bound: complementarity at bound zero alone is tautological.
  obtain ⟨hK', hI'⟩ := stable_at_of_stable f n hK hI (n + 1) (Nat.le_succ n)
  rcases Submodule.eq_bot_or_eq_bot_of_isCompl_of_indecomposable hM _ _
      (isCompl_ker_pow_range_pow_of_stable f (n + 1) hK' hI') with hker | hrange
  · right
    apply (Module.End.isUnit_iff f).mpr
    apply IsArtinian.bijective_of_injective_endomorphism
    intro x y hxy
    apply (LinearMap.ker_eq_bot.mp hker)
    simpa only [pow_succ, Module.End.mul_apply] using congrArg (f ^ n) hxy
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩

/-- The endomorphism ring of an indecomposable finite-length module is local.
See Wisbauer, *Foundations of Module and Ring Theory*, §32.4(3)(iii).
This is the classical ring-module result, with nonzeroness included in the
categorical indecomposable predicate. Only the Fitting API used in its Lean
proof is generalized to explicit one-step stability over semiring scalars and
additive-group carriers; this locality statement still assumes a ring. -/
theorem isLocalRing_of_indecomposable_of_isFiniteLength
    (hM : CategoryTheory.Indecomposable (ModuleCat.of R M))
    (hLength : IsFiniteLength R M) : IsLocalRing (Module.End R M) := by
  have hnontrivial : ¬ Subsingleton M := fun h =>
    hM.1 (ModuleCat.isZero_of_iff_subsingleton.mpr h)
  let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hnontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  rcases isNilpotent_or_isUnit_of_indecomposable_of_isFiniteLength hM hLength f with
    hnil | hunit
  · exact Or.inr hnil.isUnit_one_sub
  · exact Or.inl hunit

end Module.End
