/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Finiteness under scalar extension

Finite projectivity descends by combining finite-presentation descent with
flatness descent and Mathlib's finitely presented flat criterion. The module
retains its given additive commutative monoid and scalar action.

The faithfully flat specializations agree with Mathlib's finite-generation and
submodule-order theorems on the same algebra and modules. The order comparison
allows a noncommutative scalar ring. A linear retraction splits the tensor units
over commutative semirings; over a ring, the resulting membership and order
comparisons agree with the injective-unit comparisons.

## References

These uses combine Mathlib's finite-projective and finitely presented flat
criteria, faithfully flat descent, and tensor-product APIs.
-/

@[expose] public section

open scoped TensorProduct

universe uR uS uM uN

example (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [CommRing S] [Algebra R S]
    [Module.Finite S (S ⊗[R] M)] [Module.Projective S (S ⊗[R] M)]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.Finite R M ∧ Module.Projective R M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  let : Module.FinitePresentation S (S ⊗[R] M) :=
    Module.finitePresentation_of_projective S (S ⊗[R] M)
  let : Module.Flat R M := Module.Flat.of_flat_tensorProduct_of_injective R M S hunit
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_injective R M S hunit
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

private theorem finite_of_faithfullyFlat
    {R : Type uR} [CommRing R] (T : Type uS) [CommRing T] [Algebra R T]
    {M : Type uM} [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R T] [Module.Finite T (T ⊗[R] M)] :
    Module.Finite R M := by
  apply Module.Finite.of_finite_tensorProduct_of_injective R M T
  intro N _ _
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := T) N

example {R : Type uR} [CommRing R] (T : Type uS) [CommRing T] [Algebra R T]
    {M : Type uM} [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R T] [Module.Finite T (T ⊗[R] M)] :
    finite_of_faithfullyFlat (M := M) T =
      Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (R := R) (M := M) T :=
  Subsingleton.elim _ _

private theorem baseChange_le_iff_of_faithfullyFlat
    {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S]
    [Module.FaithfullyFlat R S] {M : Type uM} [AddCommGroup M] [Module R M]
    (N K : Submodule R M) : N.baseChange S ≤ K.baseChange S ↔ N ≤ K := by
  apply Submodule.baseChange_le_iff_of_injective
  intro P _ _
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  exact (Submodule.mem_bot R).mpr
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := R) (M := P) (A := S) x).mp
      (LinearMap.mem_ker.mp hx))

example {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S]
    [Module.FaithfullyFlat R S] {M : Type uM} [AddCommGroup M] [Module R M]
    (N K : Submodule R M) :
    baseChange_le_iff_of_faithfullyFlat (S := S) N K =
      (Submodule.baseChange_le_iff (A := S) (p := N) (q := K)) ∧
        (N.baseChange S ≤ K.baseChange S ↔ N ≤ K) := by
  exact ⟨Subsingleton.elim _ _, by simp⟩

private theorem tensorUnit_leftInverse
    {R : Type uR} {S : Type uS} [CommSemiring R] [Semiring S] [Algebra R S]
    (p : S →ₗ[R] R) (hp : p (1 : S) = 1)
    (N : Type uN) [AddCommMonoid N] [Module R N] :
    Function.LeftInverse
      ((TensorProduct.lid R N).toLinearMap.comp (p.rTensor N))
      (TensorProduct.mk R S N 1) := by
  intro n
  change p (1 : S) • n = n
  rw [hp, one_smul]

example {R : Type uR} {S : Type uS} [CommRing R] [Semiring S] [Algebra R S]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (p : S →ₗ[R] R) (hp : p (1 : S) = 1) (N K : Submodule R M) (m : M) :
    Submodule.one_tmul_mem_baseChange_iff_of_injective
        (fun P _ _ => (tensorUnit_leftInverse p hp P).injective) N m =
      Submodule.one_tmul_mem_baseChange_iff_of_linearRetraction p hp N m ∧
    Submodule.baseChange_le_iff_of_injective
        (fun P _ _ => (tensorUnit_leftInverse p hp P).injective) N K =
      Submodule.baseChange_le_iff_of_linearRetraction p hp N K :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
