/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Products and powers of matrix ideals

The entrywise matrix-ideal construction preserves products and natural-number powers of
left ideals over a semiring. Ideal multiplication uses finite sums of ordered products,
not just single products of elements.

The construction and its entrywise membership API are provided by Mathlib's `Ideal.matrix`
and `Ideal.mem_matrix`. The equalities hold for every finite index type, including the
empty type. At exponent zero, both sides are the top ideal.
-/

@[expose] public section

universe uR uI

namespace Ideal

variable {R : Type uR} [Semiring R] {ι : Type uI} [Fintype ι] [DecidableEq ι]

/-- Forming matrix ideals preserves the ordered product of left ideals. -/
theorem matrix_mul (A B : Ideal R) : (A * B).matrix ι = A.matrix ι * B.matrix ι := by
  apply le_antisymm
  · intro M hM
    rw [Matrix.matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mul_induction_on ((mem_matrix ι (A * B) M).1 hM i j) ?_ ?_
    · intro a ha b hb
      rw [← Matrix.single_mul_single_same a i i j b]
      exact mul_mem_mul ((Matrix.single_mem_matrix A.zero_mem).2 ha)
        ((Matrix.single_mem_matrix B.zero_mem).2 hb)
    · intro a b ha hb
      rw [Matrix.single_add]
      exact add_mem ha hb
  · refine mul_le.2 ?_
    intro M hM N hN
    apply (mem_matrix ι (A * B) (M * N)).2
    intro i j
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ =>
      mul_mem_mul ((mem_matrix ι A M).1 hM i k) ((mem_matrix ι B N).1 hN k j)

/-- Forming matrix ideals preserves every natural-number power, including exponent zero. -/
theorem matrix_pow (A : Ideal R) (m : ℕ) : (A ^ m).matrix ι = (A.matrix ι) ^ m := by
  induction m with
  | zero => simp only [Submodule.pow_zero, one_eq_top, matrix_top]
  | succ m ih => rw [Submodule.pow_succ, matrix_mul, ih, Submodule.pow_succ]

end Ideal
