/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.FinsuppPi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite generation and ideal multiples of dependent products

A finite dependent product of modules is finitely generated over the product of its
coefficient semirings if and only if each coordinate module is finitely generated over
its own semiring. The scalar action is the original coordinatewise action, and the
coefficient semirings need not be commutative.

Multiplication by a finitely generated ideal of one commutative semiring also commutes
with arbitrary dependent products of submodules. Finite generation gives a single finite
family of scalar generators, while the module coefficients may be chosen independently
in every coordinate. This ideal-multiple result does not require a finite index type.

## References

The constructions use Mathlib's finite generating families, linear combinations,
surjective semilinear maps, ideal multiples of spans, and dependent products of
submodules, together with `Finsupp.piLinearEquiv`.
-/

@[expose] public section

open scoped Pointwise

universe u v w

namespace Submodule

/-- Multiplication by a finitely generated ideal commutes with the full dependent
product of submodules. The coefficient semiring, index type and module carriers
have independent universes, and empty products are allowed. -/
theorem smul_pi_of_fg
    {R : Type u} [CommSemiring R] {ι : Type v} {M : ι → Type w}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (I : Ideal R) (hI : I.FG) (N : ∀ i, Submodule R (M i)) :
    I • Submodule.pi Set.univ N = Submodule.pi Set.univ (fun i ↦ I • N i) := by
  classical
  refine le_antisymm (smul_le.mpr ?_) ?_
  · intro r hr x hx
    exact mem_pi.mpr fun i hi ↦ smul_mem_smul hr (mem_pi.mp hx i hi)
  · obtain ⟨s, hs⟩ := hI
    intro x hx
    have hx' (i : ι) : x i ∈ (s : Set R) • N i := by
      rw [← coe_span_smul (s : Set R) (N i), coe_set_smul, hs]
      exact mem_pi.mp hx i (Set.mem_univ i)
    choose c hc hxc using fun i ↦ (mem_set_smul (s : Set R) (N i) (x i)).mp (hx' i)
    -- Every coordinate sum can be taken over the same finite set of scalars.
    have hsum (i : ι) : x i = ∑ r ∈ s, r • (c i r : M i) := by
      rw [hxc i,
        Finsupp.sum_of_support_subset (c i) (hc i) (fun r m ↦ r • m)
          (fun r _ ↦ smul_zero r)]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    have hxsum : x = ∑ r ∈ s, r • (fun i ↦ (c i r : M i)) := by
      ext i
      simpa only [Finset.sum_apply, Pi.smul_apply] using hsum i
    rw [hxsum]
    refine Submodule.sum_mem _ fun r hr ↦ smul_mem_smul ?_ ?_
    · rw [← hs]
      exact subset_span hr
    · exact mem_pi.mpr fun i _ ↦ (c i r).property

end Submodule

universe uι uR uM

namespace Module.Finite

/-- A finite dependent product is finitely generated over its product semiring exactly
when each coordinate is finitely generated over its own coefficient semiring. Scalars
act through the given coordinate modules, and empty products are allowed. -/
theorem piRing_iff
    {ι : Type uι} {R : ι → Type uR} {M : ι → Type uM}
    [_root_.Finite ι] [∀ i, Semiring (R i)]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)] :
    Module.Finite (∀ i, R i) (∀ i, M i) ↔ ∀ i, Module.Finite (R i) (M i) := by
  classical
  constructor
  · intro h i
    let _ := h
    let p : (∀ i, M i) →ₛₗ[Pi.evalRingHom R i] M i :=
      { toFun := fun m ↦ m i
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    apply Module.Finite.of_surjective p
    intro m
    refine ⟨Pi.single i m, ?_⟩
    change (Pi.single i m) i = m
    simp
  · intro h
    let _ : ∀ i, Module.Finite (R i) (M i) := h
    let _ : Fintype ι := Fintype.ofFinite ι
    choose n b hb using fun i ↦ Module.Finite.exists_fin (R := R i) (M := M i)
    let κ := Σ i, Fin (n i)
    let e (i : ι) : Fin (n i) ↪ κ :=
      Function.Embedding.sigmaMk (β := fun j : ι ↦ Fin (n j)) i
    -- Restriction to one summand reads that coordinate's finite generating coefficients.
    let a (i : ι) : (κ →₀ R i) →ₗ[R i] M i :=
      (Finsupp.linearCombination (R i) (b i)).comp
        (Finsupp.lcomapDomain (R := R i) (e i) (e i).injective)
    have ha (i : ι) : Function.Surjective (a i) := by
      have hb' : Function.Surjective (Finsupp.linearCombination (R i) (b i)) := by
        apply LinearMap.range_eq_top.mp
        rw [Finsupp.range_linearCombination, hb i]
      intro m
      obtain ⟨z, hz⟩ := hb' m
      refine ⟨Finsupp.mapDomain (e i) z, ?_⟩
      change Finsupp.linearCombination (R i) (b i)
        (Finsupp.lcomapDomain (R := R i) (e i) (e i).injective
          (Finsupp.mapDomain (e i) z)) = m
      rw [Finsupp.leftInverse_lcomapDomain_mapDomain (R := R i)
        (e i) (e i).injective z]
      exact hz
    let p : (∀ i, κ →₀ R i) →ₗ[∀ i, R i] (∀ i, M i) :=
      { toFun := fun z i ↦ a i (z i)
        map_add' := by
          intro z w
          exact funext fun i ↦ (a i).map_add (z i) (w i)
        map_smul' := by
          intro r z
          exact funext fun i ↦ (a i).map_smul (r i) (z i) }
    have hp : Function.Surjective p := by
      intro m
      choose z hz using fun i ↦ ha i (m i)
      exact ⟨z, funext hz⟩
    let _ : Module.Finite (∀ i, R i) (κ →₀ (∀ i, R i)) :=
      Module.Finite.equiv (Finsupp.linearEquivFunOnFinite (∀ i, R i) (∀ i, R i) κ).symm
    exact Module.Finite.of_surjective
      (p.comp (Finsupp.piLinearEquiv R R).toLinearMap)
      (hp.comp (Finsupp.piLinearEquiv R R).surjective)

end Module.Finite
