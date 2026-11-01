/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Annihilators and scalar extension

Scalars annihilating a module also annihilate its scalar extension with the
canonical left-factor action. The coefficient semiring is commutative; the
scalar algebra need not be. No finiteness or flatness is required.

## References

This is the tensor-annihilator containment used in this library's Noetherian
scalar-extension argument, formalized by Formal Frontier Agents. It uses
Mathlib's tensor balancing and annihilator APIs.
-/

@[expose] public section

universe uR uS uM

open scoped TensorProduct

/-- Every scalar annihilating a module annihilates its scalar extension, with
scalars acting on the left tensor factor. No finiteness or flatness is required. -/
theorem TensorProduct.annihilator_le_comap_annihilator
    (R : Type uR) (S : Type uS) (M : Type uM)
    [CommSemiring R] [Semiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M] :
    Module.annihilator R M ≤
      (Module.annihilator S (S ⊗[R] M)).comap (algebraMap R S) := by
  intro r hr
  apply Ideal.mem_comap.mpr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul,
      TensorProduct.smul_tmul, Module.mem_annihilator.mp hr m, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]
