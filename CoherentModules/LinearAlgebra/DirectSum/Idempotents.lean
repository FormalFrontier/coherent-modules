/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Idempotents

/-!
# Ranges of complete orthogonal endomorphisms

A finite complete orthogonal family of linear endomorphisms gives a linear equivalence
between a semimodule and the product of the endomorphism ranges. Its coordinates are the
given endomorphisms, and its inverse is the sum of the subtype inclusions. These ranges
also form an internal direct sum, with the canonical inclusion-and-sum map.

The scalar semiring need not be commutative, and the semimodule needs neither subtraction
nor cancellation. Zero ranges and empty index types are allowed; for an empty family,
completeness forces the identity endomorphism to be zero.

The construction uses Mathlib's complete orthogonal idempotents, range-restricted linear
maps, product maps and finite direct-sum comparison.
-/

@[expose] public section

universe uR uM uI

namespace CompleteOrthogonalIdempotents

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {ι : Type uI} [Fintype ι]
variable {P : ι → Module.End R M}

omit [Fintype ι] in
private theorem apply_coe_range [DecidableEq ι] (hP : OrthogonalIdempotents P)
    (i j : ι) (x : LinearMap.range (P i)) :
    P j (x : M) = if j = i then (x : M) else 0 := by
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp x.property
  rw [← hy, ← Module.End.mul_apply, hP.mul_eq]
  split_ifs with h
  · subst j
    rfl
  · rfl

/-- A semimodule is linearly equivalent to the product of the ranges of a finite complete
orthogonal family of endomorphisms. The coordinates are the given endomorphisms, and the
inverse sums the range inclusions. -/
def linearEquivPiRange (hP : CompleteOrthogonalIdempotents P) :
    M ≃ₗ[R] (∀ i, LinearMap.range (P i)) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i ↦ (P i).rangeRestrict)
    (∑ i : ι, (LinearMap.range (P i)).subtype.comp (LinearMap.proj i))
    (by
      classical
      apply LinearMap.ext
      intro y
      funext j
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.codRestrict_apply,
        LinearMap.sum_apply, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.id_apply]
      simp [map_sum, apply_coe_range hP.toOrthogonalIdempotents])
    (by
      apply LinearMap.ext
      intro x
      simpa only [LinearMap.comp_apply, LinearMap.sum_apply, Submodule.subtype_apply,
        LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.codRestrict_apply,
        LinearMap.id_apply, Module.End.one_apply] using LinearMap.congr_fun hP.complete x)

/-- The coordinate of the range equivalence is the corresponding endomorphism. -/
@[simp]
theorem linearEquivPiRange_apply (hP : CompleteOrthogonalIdempotents P) (x : M) (i : ι) :
    (hP.linearEquivPiRange x i : M) = P i x := by
  rfl

/-- The inverse of the range equivalence is the finite sum of the subtype inclusions. -/
@[simp]
theorem linearEquivPiRange_symm_apply (hP : CompleteOrthogonalIdempotents P)
    (y : ∀ i, LinearMap.range (P i)) :
    (hP.linearEquivPiRange).symm y = ∑ i, (y i : M) := by
  simp only [linearEquivPiRange, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply]

/-- The range equivalence fixes the coordinate of an element of that range. -/
@[simp]
theorem linearEquivPiRange_apply_coe_same (hP : CompleteOrthogonalIdempotents P)
    (i : ι) (x : LinearMap.range (P i)) :
    hP.linearEquivPiRange (x : M) i = x := by
  classical
  apply Subtype.ext
  rw [linearEquivPiRange_apply]
  simpa using apply_coe_range hP.toOrthogonalIdempotents i i x

/-- An element of one range has zero coordinate in every other range. -/
@[simp]
theorem linearEquivPiRange_apply_coe_ne (hP : CompleteOrthogonalIdempotents P)
    {i j : ι} (hij : i ≠ j) (x : LinearMap.range (P i)) :
    hP.linearEquivPiRange (x : M) j = 0 := by
  classical
  apply Subtype.ext
  rw [linearEquivPiRange_apply]
  simpa [hij.symm] using apply_coe_range hP.toOrthogonalIdempotents i j x

/-- On a direct sum, the inverse range equivalence is the canonical inclusion-and-sum map. -/
theorem linearEquivPiRange_symm_comp_coeFnLinearMap [DecidableEq ι]
    (hP : CompleteOrthogonalIdempotents P) :
    (hP.linearEquivPiRange).symm.toLinearMap.comp (DirectSum.coeFnLinearMap R) =
      DirectSum.coeLinearMap (fun i ↦ LinearMap.range (P i)) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  have hcoe : DirectSum.coeFnLinearMap R
      (DirectSum.lof R ι (fun i ↦ LinearMap.range (P i)) i x) = Pi.single i x :=
    rfl
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearEquiv.coe_coe]
  rw [hcoe, linearEquivPiRange_symm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- The ranges of a finite complete orthogonal family of linear endomorphisms form an
internal direct sum under their subtype inclusions. -/
theorem isInternal_range [DecidableEq ι] (hP : CompleteOrthogonalIdempotents P) :
    DirectSum.IsInternal (fun i ↦ LinearMap.range (P i)) := by
  have hbij : Function.Bijective
      ((hP.linearEquivPiRange).symm.toLinearMap.comp (DirectSum.coeFnLinearMap R)) :=
    (hP.linearEquivPiRange).symm.bijective.comp
      (DirectSum.linearEquivFunOnFintype R ι (fun i ↦ LinearMap.range (P i))).bijective
  rw [hP.linearEquivPiRange_symm_comp_coeFnLinearMap] at hbij
  exact hbij

end CompleteOrthogonalIdempotents
