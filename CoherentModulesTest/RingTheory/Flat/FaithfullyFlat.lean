/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import CoherentModulesTest.RingTheory.Flat.TensorProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.NormNum

/-!
# Surjections and faithful flatness: examples and boundaries

The second projection from a product of countably generated free abelian groups
applies `Module.FaithfullyFlat.of_surjective` with independently supplied source
flatness and target faithful flatness. Neither module is finitely generated.
Linear equivalences recover Mathlib's existing transport conclusion without
assuming source flatness separately.

Three integer-module examples isolate the hypotheses: rational numbers have
faithful scalar action but are not faithfully flat; the empty-index free module
has no surjection onto the integers; and `(ZMod 4) × ℤ` surjects onto the integers
but is not flat. The empty-index facts are supplied by the public tensor-product
example, not by accessing its private helpers.

## References

These examples use Mathlib's Finsupp and product bases, localization flatness,
the ideal-smul criterion for faithful flatness, and flatness implying torsion
freeness. The empty-index model uses
`CoherentModulesTest.Flat.TensorProduct.integerScalarEmptyBoundary`.
-/

namespace CoherentModulesTest.Flat.FaithfullyFlat

universe u v w

/-- The surjection constructor recovers faithful-flatness transport along a linear
equivalence under Mathlib's original target-faithful-flatness hypothesis. -/
public theorem linearEquivTransport
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FaithfullyFlat R N] (e : M ≃ₗ[R] N) : Module.FaithfullyFlat R M := by
  let : Module.Flat R M := Module.Flat.of_linearEquiv e
  exact Module.FaithfullyFlat.of_surjective e.toLinearMap e.surjective

/-- The second projection onto a countably generated free abelian group constructs
faithful flatness of its flat source; neither source nor target is finitely generated. -/
public theorem integerInfiniteFinsuppProjection :
    Module.Flat ℤ ((ℕ →₀ ℤ) × (ℕ →₀ ℤ)) ∧
      Module.FaithfullyFlat ℤ (ℕ →₀ ℤ) ∧
      Function.Surjective (LinearMap.snd ℤ (ℕ →₀ ℤ) (ℕ →₀ ℤ)) ∧
      Module.FaithfullyFlat ℤ ((ℕ →₀ ℤ) × (ℕ →₀ ℤ)) ∧
      ¬ Module.Finite ℤ (ℕ →₀ ℤ) ∧
      ¬ Module.Finite ℤ ((ℕ →₀ ℤ) × (ℕ →₀ ℤ)) := by
  classical
  let b : Module.Basis ℕ ℤ (ℕ →₀ ℤ) := Finsupp.basisSingleOne
  let : Module.Free ℤ (ℕ →₀ ℤ) := Module.Free.of_basis b
  let : Module.Free ℤ ((ℕ →₀ ℤ) × (ℕ →₀ ℤ)) :=
    Module.Free.prod ℤ (ℕ →₀ ℤ) (ℕ →₀ ℤ)
  let : Module.Flat ℤ ((ℕ →₀ ℤ) × (ℕ →₀ ℤ)) := Module.Flat.of_free
  let : Module.FaithfullyFlat ℤ (ℕ →₀ ℤ) := Module.FaithfullyFlat.finsupp ℤ ℕ
  have hf := LinearMap.snd_surjective (R := ℤ) (M := ℕ →₀ ℤ) (M₂ := ℕ →₀ ℤ)
  exact ⟨inferInstance, inferInstance, hf,
    Module.FaithfullyFlat.of_surjective (LinearMap.snd ℤ (ℕ →₀ ℤ) (ℕ →₀ ℤ)) hf,
    Module.not_finite_of_infinite_basis b,
    Module.not_finite_of_infinite_basis (b.prod b)⟩

private theorem integerRationalNotFaithfullyFlat : ¬ Module.FaithfullyFlat ℤ ℚ := by
  intro h
  let I : Ideal ℤ := Ideal.span ({2} : Set ℤ)
  have hproper : I ≠ ⊤ := Ideal.span_singleton_ne_top (by norm_num [Int.isUnit_iff])
  have hsmul : I • (⊤ : Submodule ℤ ℚ) = ⊤ := by
    apply top_unique
    intro q _
    have hq : (2 : ℤ) • (q / 2) = q := by
      simpa only [zsmul_eq_mul, Int.cast_ofNat] using
        (mul_div_cancel₀ q (by norm_num : (2 : ℚ) ≠ 0))
    rw [← hq]
    exact Submodule.smul_mem_smul
      (show (2 : ℤ) ∈ I from Ideal.mem_span_singleton_self 2)
      (Submodule.mem_top : q / 2 ∈ (⊤ : Submodule ℤ ℚ))
  exact hproper
    (((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top ℤ ℚ).mp h).2 I hsmul)

/-- Over the integers, the rational identity is a surjection with flat source and
faithful scalar action, but not a faithfully flat target. Thus faithful scalar action
cannot replace target faithful flatness. -/
public theorem integerRationalIdentityBoundary :
    Module.Flat ℤ ℚ ∧ FaithfulSMul ℤ ℚ ∧
      Function.Surjective (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ∧
      ¬ Module.FaithfullyFlat ℤ ℚ := by
  exact ⟨IsLocalization.flat ℚ (nonZeroDivisors ℤ), inferInstance,
    fun q ↦ ⟨q, rfl⟩, integerRationalNotFaithfullyFlat⟩

/-- The empty-index free abelian group is flat and not faithfully flat. Its zero map
has faithfully flat target `ℤ` but misses `1`, isolating the surjectivity hypothesis. -/
public theorem integerEmptyFinsuppZeroMapBoundary :
    Module.Flat ℤ (Fin 0 →₀ ℤ) ∧ Subsingleton (Fin 0 →₀ ℤ) ∧
      Module.FaithfullyFlat ℤ ℤ ∧ ¬ Module.FaithfullyFlat ℤ (Fin 0 →₀ ℤ) ∧
      ¬ Function.Surjective (0 : (Fin 0 →₀ ℤ) →ₗ[ℤ] ℤ) := by
  have h := CoherentModulesTest.Flat.TensorProduct.integerScalarEmptyBoundary
  refine ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.1, ?_⟩
  intro hf
  obtain ⟨x, hx⟩ := hf 1
  have hz : (0 : ℤ) = 1 := by simpa only [LinearMap.zero_apply] using hx
  exact zero_ne_one hz

private theorem integerZModFourProductNotFlat : ¬ Module.Flat ℤ (ZMod 4 × ℤ) := by
  intro h
  let : Module.Flat ℤ (ZMod 4 × ℤ) := h
  let : Module.IsTorsionFree ℤ (ZMod 4 × ℤ) := Module.Flat.isTorsionFree
  have hreg : IsSMulRegular (ZMod 4 × ℤ) (4 : ℤ) :=
    IsSMulRegular.of_ne_zero (by norm_num)
  have hz₁ : (4 : ℤ) • (1 : ZMod 4) = 0 := by
    simpa only [zsmul_eq_mul, Int.cast_ofNat, Nat.cast_ofNat, mul_one] using ZMod.natCast_self 4
  have hz : (4 : ℤ) • ((1 : ZMod 4), (0 : ℤ)) = (0 : ZMod 4 × ℤ) :=
    Prod.ext hz₁ (smul_zero (4 : ℤ))
  have heq : ((1 : ZMod 4), (0 : ℤ)) = (0 : ZMod 4 × ℤ) :=
    hreg (hz.trans (smul_zero (4 : ℤ)).symm)
  have hone : (1 : ZMod 4) = 0 := congrArg Prod.fst heq
  exact (by norm_num : (4 : ℕ) ≠ 1) (ZMod.one_eq_zero_iff.mp hone)

/-- The second projection from `(ZMod 4) × ℤ` is surjective onto a faithfully flat
integer module, but its source is not flat: `4` kills the nonzero element `(1, 0)`. -/
public theorem integerZModFourProjectionBoundary :
    Module.FaithfullyFlat ℤ ℤ ∧
      Function.Surjective (LinearMap.snd ℤ (ZMod 4) ℤ) ∧
      ¬ Module.Flat ℤ (ZMod 4 × ℤ) ∧ ¬ Module.FaithfullyFlat ℤ (ZMod 4 × ℤ) := by
  refine ⟨Module.FaithfullyFlat.self ℤ, LinearMap.snd_surjective,
    integerZModFourProductNotFlat, ?_⟩
  intro h
  exact integerZModFourProductNotFlat h.toFlat

end CoherentModulesTest.Flat.FaithfullyFlat
