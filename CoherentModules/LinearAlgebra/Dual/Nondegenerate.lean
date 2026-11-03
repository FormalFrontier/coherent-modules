/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Nondegeneracy of self-pairings

A surjective linear map from a semimodule to its own dual is nondegenerate
provided it separates the left slot. In particular, every bijective such map
is nondegenerate. The proof uses the flipped bilinear form, with no reflexivity
or finiteness assumption on the semimodule.
-/

@[expose] public section

universe u v

namespace LinearMap

variable {R : Type u} {V : Type v}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- A surjective self-pairing that separates the left slot is nondegenerate in both slots. -/
theorem nondegenerate_of_surjective_of_separatingLeft
    (B : V →ₗ[R] Module.Dual R V) (hs : Function.Surjective B)
    (hl : B.SeparatingLeft) : B.Nondegenerate := by
  refine ⟨hl, ?_⟩
  intro w hw
  apply hl w
  intro x
  obtain ⟨v, hv⟩ := hs (B.flip x)
  calc
    B w x = B.flip x w := (LinearMap.flip_apply B w x).symm
    _ = B v w := by rw [hv]
    _ = 0 := hw v

/-- A bijective linear map from a semimodule to its own dual is a nondegenerate bilinear form. -/
theorem nondegenerate_of_bijective (B : V →ₗ[R] Module.Dual R V)
    (hB : Function.Bijective B) : B.Nondegenerate := by
  apply B.nondegenerate_of_surjective_of_separatingLeft hB.2
  apply separatingLeft_iff_linear_nontrivial.mpr
  intro x hx
  exact hB.1 (hx.trans B.map_zero.symm)

end LinearMap
