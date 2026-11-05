/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Spans intersected with kernels having conical targets

If a linear map's target has no nonzero summands of zero and no zero scalar
divisors, its kernel selects generators: intersecting an arbitrary span with the
kernel is the span of the generators already in the kernel. Filtering a finite
generating set consequently preserves finite generation.

The range-restriction corollaries require these properties only on the image of
the map, not on its ambient codomain, and retain the original kernel.
-/

@[expose] public section

universe uR uM uN

namespace Submodule

variable {R : Type uR} {M : Type uM} {N : Type uN}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- For a target with no nonzero additive summands of zero and no zero scalar
divisors, intersecting a span with a kernel selects exactly its kernel generators. -/
theorem span_inf_ker_eq_span_inter [NoZeroSMulDivisors R N]
    (f : M →ₗ[R] N) (S : Set M)
    (hN : ∀ ⦃a b : N⦄, a + b = 0 → a = 0 ∧ b = 0) :
    span R S ⊓ LinearMap.ker f = span R (S ∩ (LinearMap.ker f : Set M)) := by
  apply le_antisymm
  · intro x hx
    have hx0 := LinearMap.mem_ker.mp hx.2
    refine span_induction (p := fun x _ =>
      f x = 0 → x ∈ span R (S ∩ (LinearMap.ker f : Set M))) ?_ ?_ ?_ ?_ hx.1 hx0
    · intro y hy hy0
      exact subset_span ⟨hy, LinearMap.mem_ker.mpr hy0⟩
    · intro _
      exact zero_mem _
    · intro a b _ _ ha hb hab
      have h := hN (a := f a) (b := f b) (by simpa only [map_add] using hab)
      exact add_mem (ha h.1) (hb h.2)
    · intro c y _ hy hcy
      rcases eq_zero_or_eq_zero_of_smul_eq_zero (c := c) (x := f y)
          (by simpa only [map_smul] using hcy) with hc | hy0
      · subst c
        simpa only [zero_smul] using (zero_mem (span R (S ∩ (LinearMap.ker f : Set M))))
      · exact smul_mem _ c (hy hy0)
  · refine span_le.mpr ?_
    intro x hx
    exact ⟨subset_span hx.1, hx.2⟩

/-- Intersecting a finitely generated submodule with a kernel preserves finite
generation when the target reflects zero sums and zero scalar multiples. -/
theorem FG.inf_ker [NoZeroSMulDivisors R N] {K : Submodule R M} (hK : K.FG)
    (f : M →ₗ[R] N)
    (hN : ∀ ⦃a b : N⦄, a + b = 0 → a = 0 ∧ b = 0) :
    (K ⊓ LinearMap.ker f).FG := by
  obtain ⟨S, hS, rfl⟩ := fg_def.mp hK
  rw [span_inf_ker_eq_span_inter f S hN]
  exact fg_span (hS.inter_of_left _)

/-- It suffices that zero sums and zero scalar multiples are reflected in the
image of the map; no such condition on the ambient codomain is required. -/
theorem span_inf_ker_eq_span_inter_of_range (f : M →ₗ[R] N)
    [NoZeroSMulDivisors R (LinearMap.range f)] (S : Set M)
    (hN : ∀ ⦃a b : LinearMap.range f⦄, a + b = 0 → a = 0 ∧ b = 0) :
    span R S ⊓ LinearMap.ker f = span R (S ∩ (LinearMap.ker f : Set M)) := by
  simpa only [LinearMap.ker_rangeRestrict] using
    span_inf_ker_eq_span_inter f.rangeRestrict S hN

/-- A finitely generated submodule has finitely generated intersection with the
kernel if zero sums and zero scalar multiples are reflected in the image. -/
theorem FG.inf_ker_of_range {K : Submodule R M} (hK : K.FG) (f : M →ₗ[R] N)
    [NoZeroSMulDivisors R (LinearMap.range f)]
    (hN : ∀ ⦃a b : LinearMap.range f⦄, a + b = 0 → a = 0 ∧ b = 0) :
    (K ⊓ LinearMap.ker f).FG := by
  simpa only [LinearMap.ker_rangeRestrict] using hK.inf_ker f.rangeRestrict hN

end Submodule
