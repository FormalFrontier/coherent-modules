/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Uses of flatness descent along pure scalar extension

The descended flatness class preserves injectivity after tensoring original
modules in independent universes, even when the original flat module has only
an additive commutative monoid structure in the statement.

The faithfully flat specializations recover Mathlib's original descent theorem
and its iff, with their given algebra and additive group data. Their tensor-unit
hypotheses also handle weak test modules by deriving the canonical group
structure internally.
-/

@[expose] public section

open scoped TensorProduct

universe uR uS uM uN uP

example {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN} {P : Type uP}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module.Flat S (S ⊗[R] M)]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    (hunit : ∀ (Q : Type (max uR uM)) [AddCommMonoid Q] [Module R Q],
      Function.Injective (TensorProduct.mk R S Q 1))
    (f : N →ₗ[R] P) (hf : Function.Injective f) :
    Function.Injective (f.rTensor M) := by
  let : Module.Flat R M := Module.Flat.of_flat_tensorProduct_of_injective R M S hunit
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

example (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    (S : Type uS) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.Flat S (S ⊗[R] M)] : Module.Flat R M := by
  apply Module.Flat.of_flat_tensorProduct_of_injective R M S
  intro N _ _
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) N

example (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
    (S : Type uS) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M := by
  apply Module.Flat.iff_flat_tensorProduct_of_injective R M S
  intro N _ _
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) N
