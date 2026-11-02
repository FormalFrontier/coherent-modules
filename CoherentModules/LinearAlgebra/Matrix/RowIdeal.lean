/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Left matrix ideals and row submodules

For a finite index type `I`, left ideals of `Matrix I I R` correspond to
`R`-submodules of the row module `I → R`. The correspondence uses the existing
pointwise left action on rows and works over an arbitrary semiring, including
an empty index type or the zero semiring.

* `Submodule.matrixRows` consists of matrices whose rows lie in a submodule.
* `Ideal.rowSubmodule` tests insertion of a row into every row position.
* `Submodule.matrixRowsOrderIso` gives the order isomorphism.
* `Matrix.isArtinianRing_iff_rowModule` and
  `Matrix.isNoetherianRing_iff_rowModule` transport the two chain conditions.

The row module in these last statements is essential: these are not unrestricted
semiring ascent statements from the coefficient ring. The construction concerns
left ideals, not two-sided ideals. `Ideal.matrixRows_pi` identifies the special
case arising from an entrywise coefficient ideal with Mathlib's `Ideal.matrix`.
-/

@[expose] public section

universe u v

variable {R : Type u} [Semiring R] {I : Type v} [Fintype I] [DecidableEq I]

private lemma single_mul_eq_single_row (i j : I) (r : R) (A : Matrix I I R) :
    Matrix.single i j r * A = Matrix.of (Pi.single i (r • A j)) := by
  ext k l
  by_cases h : k = i
  · subst k
    simp [Pi.smul_apply, smul_eq_mul]
  · simp [Matrix.single_mul_apply_of_ne, h]

namespace Submodule

/-- The left ideal of matrices all of whose rows lie in `S`. -/
def matrixRows (S : Submodule R (I → R)) : Ideal (Matrix I I R) where
  __ := (Submodule.pi Set.univ fun _ : I => S).toAddSubmonoid
  smul_mem' B A hA := by
    intro i _
    change (B * A) i ∈ S
    have hrow : (B * A) i = ∑ k, B i k • A k := by
      ext j
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrow]
    exact S.sum_mem fun k _ => S.smul_mem (B i k) (hA k (Set.mem_univ k))

@[simp]
theorem mem_matrixRows (S : Submodule R (I → R)) (A : Matrix I I R) :
    A ∈ S.matrixRows ↔ ∀ i, A i ∈ S := by
  change (∀ i ∈ Set.univ, A i ∈ S) ↔ ∀ i, A i ∈ S
  simp

theorem matrixRows_monotone : Monotone (matrixRows (R := R) (I := I)) := by
  intro S T h A hA
  exact (mem_matrixRows T A).mpr fun i => h ((mem_matrixRows S A).mp hA i)

end Submodule

namespace Ideal

/-- The row submodule of a left matrix ideal: inserting the row into any row
position gives an element of the ideal. -/
def rowSubmodule (J : Ideal (Matrix I I R)) : Submodule R (I → R) where
  carrier := {v | ∀ i, Matrix.of (Pi.single i v) ∈ J}
  zero_mem' := by
    intro i
    rw [Pi.single_zero, Matrix.of_zero]
    exact J.zero_mem
  add_mem' := by
    intro v w hv hw i
    rw [Pi.single_add, ← Matrix.of_add_of]
    exact J.add_mem (hv i) (hw i)
  smul_mem' := by
    intro r v hv i
    have hi : (Matrix.of (Pi.single i v)) i = v := by ext j; simp
    have h := J.mul_mem_left (Matrix.single i i r) (hv i)
    rw [single_mul_eq_single_row, hi] at h
    exact h

@[simp]
theorem mem_rowSubmodule (J : Ideal (Matrix I I R)) (v : I → R) :
    v ∈ J.rowSubmodule ↔ ∀ i, (Pi.single i v : Matrix I I R) ∈ J :=
  Iff.rfl

theorem rowSubmodule_monotone : Monotone (rowSubmodule (R := R) (I := I)) := by
  intro J K h v hv
  exact (mem_rowSubmodule K v).mpr fun i => h ((mem_rowSubmodule J v).mp hv i)

end Ideal

namespace Submodule

@[simp]
theorem rowSubmodule_matrixRows (S : Submodule R (I → R)) :
    S.matrixRows.rowSubmodule = S := by
  ext v
  constructor
  · intro hv
    rcases isEmpty_or_nonempty I with hI | hI
    · -- An empty index type has only the zero row; no index is selected.
      let := hI
      have hv0 : v = 0 := Subsingleton.elim _ _
      simpa only [hv0] using S.zero_mem
    · obtain ⟨i⟩ := hI
      simpa using (mem_matrixRows S _).mp ((Ideal.mem_rowSubmodule _ _).mp hv i) i
  · intro hv
    apply (Ideal.mem_rowSubmodule _ _).mpr
    intro i
    apply (mem_matrixRows S _).mpr
    intro j
    by_cases h : j = i
    · subst j
      simpa using hv
    · simp [Ne.symm h]

end Submodule

namespace Ideal

@[simp]
theorem matrixRows_rowSubmodule (J : Ideal (Matrix I I R)) :
    J.rowSubmodule.matrixRows = J := by
  ext A
  constructor
  · intro hA
    have hrows := (Submodule.mem_matrixRows _ _).mp hA
    have hsum : ∑ i, Matrix.of (Pi.single i (A i)) = A := by
      ext i j
      have h := congrFun (congrFun
        (LinearMap.sum_single_apply (fun _ : I => I → R) A) i) j
      simpa only [Finset.sum_apply, Matrix.sum_apply, Matrix.of_apply] using h
    rw [← hsum]
    exact J.sum_mem fun i _ => (mem_rowSubmodule _ _).mp (hrows i) i
  · intro hA
    apply (Submodule.mem_matrixRows _ _).mpr
    intro i
    apply (mem_rowSubmodule _ _).mpr
    intro j
    change Matrix.of (Pi.single j (A i)) ∈ J
    have h : Matrix.of (Pi.single j (A i)) = Matrix.single j i 1 * A := by
      simpa only [one_smul] using (single_mul_eq_single_row j i 1 A).symm
    rw [h]
    exact J.mul_mem_left (Matrix.single j i 1) hA

/-- Entrywise coefficient ideals are the special case of the row construction
where every coordinate of each row belongs to the coefficient ideal. -/
@[simp]
theorem matrixRows_pi (L : Ideal R) :
    (Submodule.pi Set.univ (fun _ : I => (L : Submodule R R))).matrixRows = L.matrix I := by
  ext A
  simp [Submodule.mem_matrixRows, Submodule.mem_pi, Ideal.mem_matrix]

end Ideal

namespace Submodule

/-- The order isomorphism between submodules of the row module and left matrix
ideals, valid also for an empty index type. -/
def matrixRowsOrderIso : Submodule R (I → R) ≃o Ideal (Matrix I I R) where
  toFun := matrixRows
  invFun := Ideal.rowSubmodule
  left_inv := rowSubmodule_matrixRows
  right_inv := Ideal.matrixRows_rowSubmodule
  map_rel_iff' := by
    intro S T
    change S.matrixRows ≤ T.matrixRows ↔ S ≤ T
    constructor
    · intro h
      simpa only [rowSubmodule_matrixRows] using Ideal.rowSubmodule_monotone h
    · exact fun h => matrixRows_monotone h

@[simp]
theorem matrixRowsOrderIso_apply (S : Submodule R (I → R)) :
    matrixRowsOrderIso S = S.matrixRows := rfl

@[simp]
theorem matrixRowsOrderIso_symm_apply (J : Ideal (Matrix I I R)) :
    matrixRowsOrderIso.symm J = J.rowSubmodule := rfl

@[simp]
theorem matrixRows_le_matrixRows_iff {S T : Submodule R (I → R)} :
    S.matrixRows ≤ T.matrixRows ↔ S ≤ T :=
  matrixRowsOrderIso.le_iff_le

end Submodule

namespace Ideal

@[simp]
theorem rowSubmodule_le_rowSubmodule_iff {J K : Ideal (Matrix I I R)} :
    J.rowSubmodule ≤ K.rowSubmodule ↔ J ≤ K :=
  Submodule.matrixRowsOrderIso.symm.le_iff_le

end Ideal

namespace Matrix

/-- A matrix semiring is left Artinian exactly when its row module is Artinian.
This does not require the coefficient semiring to be a ring. -/
theorem isArtinianRing_iff_rowModule :
    IsArtinianRing (Matrix I I R) ↔ IsArtinian R (I → R) := by
  change IsArtinian (Matrix I I R) (Matrix I I R) ↔ IsArtinian R (I → R)
  rw [isArtinian_iff, isArtinian_iff]
  let e := Submodule.matrixRowsOrderIso (R := R) (I := I)
  exact (e.surjective.wellFounded_iff (fun {_ _} => e.lt_iff_lt.symm)).symm

/-- A matrix semiring is left Noetherian exactly when its row module is Noetherian.
The row module cannot in general be replaced by the coefficient semiring. -/
theorem isNoetherianRing_iff_rowModule :
    IsNoetherianRing (Matrix I I R) ↔ IsNoetherian R (I → R) := by
  change IsNoetherian (Matrix I I R) (Matrix I I R) ↔ IsNoetherian R (I → R)
  rw [isNoetherian_iff, isNoetherian_iff]
  let e := Submodule.matrixRowsOrderIso (R := R) (I := I)
  exact (e.surjective.wellFounded_iff (r := (· > ·)) (s := (· > ·))
    (fun {S T} => show T < S ↔ e T < e S from e.lt_iff_lt.symm)).symm

end Matrix
