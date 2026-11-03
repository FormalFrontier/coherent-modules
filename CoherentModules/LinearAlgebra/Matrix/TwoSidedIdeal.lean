/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The matrix-ideal argument is adapted from Mathlib.LinearAlgebra.Matrix.Ideal:
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CoherentModules.RingTheory.Ideal.TwoSided
public import Mathlib.LinearAlgebra.Matrix.Ideal

/-!
# Two-sided ideals of a matrix semiring

`Ideal.twoSidedMatrixOrderIso` identifies the two-sided ideals of a semiring with those
of its square matrix semiring. The forward map is Mathlib's entrywise `Ideal.matrix`;
the inverse is `Ideal.comap` along the unital diagonal homomorphism `Matrix.scalar`.
The coefficient semiring and both canonical left regular actions are unchanged.

The characteristic lemmas describe the underlying ideals and membership. Inverse,
order, and lattice identities are available through the general `OrderIso` API.
Over rings, `TwoSidedIdeal.orderIsoIsTwoSided_trans_twoSidedMatrixOrderIso` compares
this correspondence with Mathlib's correspondence on `TwoSidedIdeal`.

## Implementation notes

The finite index type is required to be nonempty: for an empty index type the matrix
semiring has one element, so its ideals cannot classify arbitrary coefficient ideals.
The coefficient semiring itself may have one element. No commutativity of coefficients
or centrality of scalar matrices is assumed. Associative semirings and the nonassociative
rings allowed by Mathlib's `TwoSidedIdeal.orderIsoMatrix` are different generality axes;
the comparison here concerns their overlap at associative rings.

## Credits

The correspondence is adapted from the matrix-ideal formalization by Jujian Zhang and
Wojciech Nawrocki in Mathlib's `LinearAlgebra/Matrix/Ideal.lean`. It uses the existing
`Ideal.matrix`, `Matrix.scalar`, and `TwoSidedIdeal.orderIsoIsTwoSided` constructions;
ordinary semiring ideals are not replaced by congruence kernels.
-/

@[expose] public section

universe uR uι

namespace Ideal

variable {R : Type uR} [Semiring R]
    (ι : Type uι) [Fintype ι] [DecidableEq ι]

/-- A two-sided ideal of a matrix semiring is recovered from its pullback along
scalar diagonal matrices. This holds even when the index type is empty. -/
theorem matrix_comap_scalar_of_isTwoSided (J : Ideal (Matrix ι ι R))
    (hJ : J.IsTwoSided) : (comap (Matrix.scalar ι) J).matrix ι = J := by
  let : J.IsTwoSided := hJ
  apply le_antisymm
  · intro X hX
    rw [Matrix.matrix_eq_sum_single X]
    refine Submodule.sum_mem J fun i _ => Submodule.sum_mem J fun j _ => ?_
    have hscalar : Matrix.scalar ι (X i j) ∈ J :=
      mem_comap.mp ((mem_matrix ι _ _).mp hX i j)
    have hsingle : Matrix.single i j (1 : R) * Matrix.scalar ι (X i j) =
        Matrix.single i j (X i j) := by
      ext a b
      simp [Matrix.scalar_apply, Matrix.single, ite_mul]
    rw [← hsingle]
    exact J.mul_mem_left _ hscalar
  · intro X hX
    rw [mem_matrix]
    intro i j
    rw [mem_comap, Matrix.scalar_apply, ← Matrix.sum_single_eq_diagonal]
    refine Submodule.sum_mem J fun k _ => ?_
    simpa only [Matrix.single_mul_mul_single, one_mul, mul_one] using
      (Ideal.mul_mem_right (Matrix.single j k (1 : R)) J
        (J.mul_mem_left (Matrix.single k i (1 : R)) hX))

variable [Nonempty ι]

/-- Two-sided ideals of a semiring correspond, in order, to two-sided ideals of its
square matrix semiring. The forward map takes matrices with entries in the ideal;
the inverse pulls back along the unital scalar diagonal homomorphism. -/
def twoSidedMatrixOrderIso : twoSidedIdeals R ≃o twoSidedIdeals (Matrix ι ι R) where
  toFun A := ⟨A.val.matrix ι, by
    apply (mem_twoSidedIdeals _).mpr
    have : A.val.IsTwoSided := A.property
    constructor
    intro X Y hX
    rw [mem_matrix] at hX ⊢
    intro i j
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ => A.val.mul_mem_right _ (hX i k)⟩
  invFun J := ⟨comap (Matrix.scalar ι) J.val, by
    apply (mem_twoSidedIdeals _).mpr
    have : J.val.IsTwoSided := J.property
    infer_instance⟩
  left_inv A := by
    apply Subtype.ext
    ext r
    simp only [mem_comap, mem_matrix, Matrix.scalar_apply]
    constructor
    · intro h
      obtain ⟨i⟩ := ‹Nonempty ι›
      simpa only [Matrix.diagonal_apply_eq] using h i i
    · intro hr i j
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.diagonal_apply_eq] using hr
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact A.val.zero_mem
  right_inv J := by
    apply Subtype.ext
    exact matrix_comap_scalar_of_isTwoSided ι J.val J.property
  map_rel_iff' {A B} := by
    constructor
    · intro h r hr
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hmem : Matrix.of (fun (_ _ : ι) => r) ∈ A.val.matrix ι :=
        (mem_matrix ι _ _).2 fun _ _ => hr
      exact ((mem_matrix ι _ _).1 (h hmem)) i i
    · intro h
      exact matrix_monotone ι h

/-- The underlying forward ideal is the entrywise matrix ideal. -/
@[simp] theorem coe_twoSidedMatrixOrderIso_apply (A : twoSidedIdeals R) :
    (twoSidedMatrixOrderIso (R := R) ι A).val = A.val.matrix ι := rfl

/-- The underlying inverse ideal is the pullback along scalar diagonal matrices. -/
@[simp] theorem coe_twoSidedMatrixOrderIso_symm_apply
    (J : twoSidedIdeals (Matrix ι ι R)) :
    ((twoSidedMatrixOrderIso (R := R) ι).symm J).val =
      comap (Matrix.scalar ι) J.val := rfl

/-- Forward membership means that every matrix entry belongs to the coefficient ideal. -/
theorem mem_twoSidedMatrixOrderIso_apply (A : twoSidedIdeals R)
    (X : Matrix ι ι R) :
    X ∈ (twoSidedMatrixOrderIso (R := R) ι A).val ↔ ∀ i j, X i j ∈ A.val := by
  rw [coe_twoSidedMatrixOrderIso_apply, mem_matrix]

/-- Inverse membership is membership of the scalar diagonal matrix. -/
theorem mem_twoSidedMatrixOrderIso_symm_apply
    (J : twoSidedIdeals (Matrix ι ι R)) (r : R) :
    r ∈ ((twoSidedMatrixOrderIso (R := R) ι).symm J).val ↔
      Matrix.scalar ι r ∈ J.val := by
  rw [coe_twoSidedMatrixOrderIso_symm_apply, mem_comap]

end Ideal

namespace TwoSidedIdeal

variable {R : Type uR} [Ring R]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- On rings, the matrix correspondence on two-sided ordinary ideals agrees with
Mathlib's correspondence after identifying `TwoSidedIdeal` with that subtype. -/
theorem orderIsoIsTwoSided_trans_twoSidedMatrixOrderIso :
    (orderIsoIsTwoSided (R := R)).trans (Ideal.twoSidedMatrixOrderIso (R := R) ι) =
      (orderIsoMatrix (R := R) (n := ι)).trans
        (orderIsoIsTwoSided (R := Matrix ι ι R)) := by
  apply OrderIso.ext
  funext A
  apply Subtype.ext
  exact (asIdeal_matrix (n := ι) A).symm

end TwoSidedIdeal
