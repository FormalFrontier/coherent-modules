/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Scalar extension of ideal multiples

Scalar extension carries the action of an ideal on a submodule to the action of
its extended ideal on the extended submodule. The coefficient semiring is
commutative, but the scalar algebra need not be. No flatness or finiteness
hypothesis is required, and the module may be only an additive commutative monoid.

Centrality of the algebra map allows its image to commute with the left-factor
scalar action on the tensor product.

## References

The formalization uses Mathlib's submodule base change, ideal map, ideal action,
span induction and tensor balancing APIs.
-/

@[expose] public section

universe uR uA uM

open scoped Pointwise TensorProduct

namespace Submodule

/-- Scalar extension commutes with the action of an ideal on a submodule, using
its extended ideal and the canonical left-factor action on the tensor product.
The scalar algebra need not be commutative; no flatness or finiteness is needed. -/
theorem baseChange_smul
    {R : Type uR} {A : Type uA} [CommSemiring R] [Semiring A]
    [Algebra R A] {M : Type uM} [AddCommMonoid M] [Module R M]
    (I : Ideal R) (N : Submodule R M) :
    (I • N).baseChange A = (I.map (algebraMap R A)) • N.baseChange A := by
  apply le_antisymm
  · rw [baseChange_eq_span]
    refine span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    change (1 : A) ⊗ₜ[R] m ∈ (I.map (algebraMap R A)) • N.baseChange A
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr m hm
      simpa only [TensorProduct.mk_apply, IsScalarTower.algebraMap_smul,
        TensorProduct.tmul_smul] using
        (smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R A) hr)
          (tmul_mem_baseChange_of_mem (A := A) 1 hm))
    · intro x y hx hy
      simpa only [TensorProduct.tmul_add] using
        ((I.map (algebraMap R A)) • N.baseChange A).add_mem hx hy
  · refine smul_le.mpr fun a ha x hx => ?_
    change a ∈ span A (algebraMap R A '' (I : Set R)) at ha
    refine span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨r, hr, rfl⟩
      rw [baseChange_eq_span] at hx
      refine span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨m, hm, rfl⟩
        simpa only [TensorProduct.mk_apply, IsScalarTower.algebraMap_smul,
          TensorProduct.tmul_smul] using
          (tmul_mem_baseChange_of_mem (A := A) 1 (smul_mem_smul hr hm))
      · simpa only [smul_zero] using ((I • N).baseChange A).zero_mem
      · intro y z _ _ hy hz
        simpa only [smul_add] using ((I • N).baseChange A).add_mem hy hz
      · intro b y _ hy
        rw [IsScalarTower.algebraMap_smul, smul_comm r b]
        exact ((I • N).baseChange A).smul_mem b
          (by simpa only [IsScalarTower.algebraMap_smul] using hy)
    · simpa only [zero_smul] using ((I • N).baseChange A).zero_mem
    · intro b c _ _ hb hc
      simpa only [add_smul] using ((I • N).baseChange A).add_mem hb hc
    · intro b c _ hc
      simpa only [smul_eq_mul, mul_smul] using ((I • N).baseChange A).smul_mem b hc

end Submodule
