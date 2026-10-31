/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Unit-ideal scalar families in semimodules

A family of scalars generating the unit ideal recovers a unique common parameter from
compatible semimodule elements. The index type is arbitrary, and the scalar actions
need only commute on the semimodule. Neither subtraction nor additive cancellation
is needed.

For two scalars, a Bézout identity gives this gluing principle. Here `IsCoprime a b`
means that `r * a + s * b = 1` for some scalars `r, s`, not merely that `a` and `b`
have no common nonunit divisor. The range-membership criterion specializes to
Mathlib's coprime divisibility criterion on the regular semimodule.

## References

The family theorem applies Kenny Lau's scalar-span membership principle
`Submodule.mem_of_span_top_of_smul_mem` in `Mathlib.RingTheory.Ideal.Operations`,
together with Mathlib's linear-map Pi and equality-on-span APIs. The pair results
use Mathlib's Bézout definition of `IsCoprime` and its scalar divisibility API in
`Mathlib.RingTheory.Coprime.Basic`.
-/

@[expose] public section

universe u v w

namespace Ideal

/-- A compatible family has a unique common parameter when its scalars generate the
unit ideal and their actions commute on the semimodule. The index type need not be
finite or nonempty, and the semimodule needs no additive inverses or cancellation. -/
theorem existsUnique_smul_eq_of_span_range_eq_top
    {S : Type u} [Semiring S]
    {M : Type v} [AddCommMonoid M] [Module S M] [SMulCommClass S S M]
    {ι : Type w} (a : ι → S) (hspan : Ideal.span (Set.range a) = ⊤)
    (x : ι → M) (hcompat : ∀ i j, a j • x i = a i • x j) :
    ∃! k : M, ∀ i, a i • k = x i := by
  let D : M →ₗ[S] (ι → M) := LinearMap.pi fun i => DistribSMul.toLinearMap S M (a i)
  have hx : x ∈ LinearMap.range D := by
    apply Submodule.mem_of_span_top_of_smul_mem (LinearMap.range D) (Set.range a) hspan x
    rintro ⟨_, i, rfl⟩
    refine ⟨x i, ?_⟩
    funext j
    exact hcompat i j
  obtain ⟨k, hk⟩ := hx
  have hk' : ∀ i, a i • k = x i := fun i => congrFun hk i
  refine ⟨k, hk', fun y hy => ?_⟩
  apply LinearMap.toSpanSingleton_injective S M
  apply LinearMap.ext_on_range hspan
  intro i
  exact (hy i).trans (hk' i).symm

end Ideal

namespace IsCoprime

variable {S : Type u} [CommSemiring S]
variable {M : Type v} [AddCommMonoid M] [Module S M]
variable {a b : S}

/-- A compatible pair has a unique common parameter when the two scalars satisfy
Bézout's identity. This holds for semimodules without additive inverses or cancellation. -/
theorem existsUnique_smul_eq_pair (h : IsCoprime a b) {x y : M}
    (hxy : b • x = a • y) : ∃! k : M, a • k = x ∧ b • k = y := by
  obtain ⟨r, s, hrs⟩ := h
  let k := r • x + s • y
  have hak : a • k = x := by
    calc
      a • k = r • (a • x) + s • (a • y) := by
        dsimp only [k]
        rw [smul_add, smul_comm a r x, smul_comm a s y]
      _ = r • (a • x) + s • (b • x) := by rw [hxy]
      _ = (r * a + s * b) • x := by rw [add_smul, mul_smul, mul_smul]
      _ = x := by rw [hrs, one_smul]
  have hbk : b • k = y := by
    calc
      b • k = r • (b • x) + s • (b • y) := by
        dsimp only [k]
        rw [smul_add, smul_comm b r x, smul_comm b s y]
      _ = r • (a • y) + s • (b • y) := by rw [hxy]
      _ = (r * a + s * b) • y := by rw [add_smul, mul_smul, mul_smul]
      _ = y := by rw [hrs, one_smul]
  refine ⟨k, ⟨hak, hbk⟩, ?_⟩
  rintro z ⟨haz, hbz⟩
  calc
    z = (r * a + s * b) • z := by rw [hrs, one_smul]
    _ = r • (a • z) + s • (b • z) := by rw [add_smul, mul_smul, mul_smul]
    _ = r • x + s • y := by rw [haz, hbz]
    _ = k := rfl

/-- Multiplication by a coprime scalar reflects membership in the range of a scalar
multiplication map. On the regular semimodule this is coprime divisibility cancellation. -/
theorem smul_mem_range_smul_iff (h : IsCoprime a b) (x : M) :
    b • x ∈ Set.range (fun y : M ↦ a • y) ↔ x ∈ Set.range (fun y : M ↦ a • y) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, hk, _⟩ := h.existsUnique_smul_eq_pair hy.symm
    exact ⟨k, hk.1⟩
  · rintro ⟨y, rfl⟩
    exact ⟨b • y, smul_comm a b y⟩

end IsCoprime
