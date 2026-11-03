/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Internal realization of a direct sum

A supplied linear equivalence from an external direct sum to a semimodule realizes
its summands as an internal direct sum of submodules: take the ranges of the
singleton inclusions followed by the equivalence. Internality refers to the
canonical inclusion-and-sum map `DirectSum.coeLinearMap`, not merely to the
existence of an abstract equivalence of totals.

The scalar semiring, index type, summand carriers and total carrier have
independent universes. The singleton inclusions and internality use the caller's
`DecidableEq` instance on the index type. Neither finiteness nor additive inverses
are needed.

## References

Mathlib's `Algebra.DirectSum.Module` supplies the singleton inclusions, the
canonical inclusion-and-sum map and `DirectSum.congrLinearEquiv`.
`LinearEquiv.ofInjective` identifies each summand with the range of its inclusion.
-/

@[expose] public section

universe uR uI uA uM

namespace DirectSum

variable {R : Type uR} [Semiring R]
variable {ι : Type uI} [DecidableEq ι] {A : ι → Type uA}
variable [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- The ranges of the summand inclusions of a supplied direct-sum linear equivalence
form an internal direct sum. The singleton inclusions and internality use the
caller's equality instance. The map certifying internality is the canonical sum
of the subtype inclusions of these ranges. -/
theorem isInternal_range_comp_lof (e : (⨁ i, A i) ≃ₗ[R] M) :
    IsInternal (fun i ↦ LinearMap.range (e.toLinearMap.comp (lof R ι A i))) := by
  let f : ∀ i, A i →ₗ[R] M := fun i ↦ e.toLinearMap.comp (lof R ι A i)
  have hf (i : ι) : Function.Injective (f i) :=
    e.injective.comp (of_injective i)
  let u : ∀ i, A i ≃ₗ[R] LinearMap.range (f i) :=
    fun i ↦ LinearEquiv.ofInjective (f i) (hf i)
  let E := congrLinearEquiv u
  have h : (coeLinearMap (fun i ↦ LinearMap.range (f i))).comp E.toLinearMap =
      e.toLinearMap := by
    apply linearMap_ext
    intro i
    ext x
    simp [E, congrLinearEquiv_toLinearMap, u, f]
  change Function.Bijective (coeLinearMap (fun i ↦ LinearMap.range (f i)))
  apply (Function.Bijective.of_comp_iff _ E.bijective).mp
  change Function.Bijective ((coeLinearMap (fun i ↦ LinearMap.range (f i))).comp
    E.toLinearMap)
  rw [h]
  exact e.bijective

end DirectSum
