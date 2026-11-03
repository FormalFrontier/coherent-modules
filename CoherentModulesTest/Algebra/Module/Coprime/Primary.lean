/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.Module.Coprime.Kernel
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Primary kernels from a nonzero polynomial annihilator

This application of `Polynomial.linearEquivPiKer` takes the distinct monic
irreducibles in Mathlib's `UniqueFactorizationMonoid.normalizedFactors` and their
exact multiset counts. Its target consists of the ordinary kernels of powers of
polynomial evaluations, over the original scalar field.

The product is formed in the commutative polynomial ring before evaluation.
Mapping and cancelling the leading unit needs no injectivity of the scalar
representation, so the zero module and nonzero constant annihilators are included.
No finite-dimensional hypothesis or polynomial module structure is used.

## References

The factorization, coprimality and unit-cancellation inputs use Mathlib's polynomial
and unique-factorization APIs. The equivalence is supplied by
`Polynomial.linearEquivPiKer` in `CoherentModules.Algebra.Module.Coprime.Kernel`.
-/

open Polynomial UniqueFactorizationMonoid

universe uK uV

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommMonoid V] [Module K V]

open Classical in
/-- A nonzero annihilator supplies all inputs to the coprime-kernel equivalence,
with the normalized irreducibles indexed once and raised to their exact counts. -/
private noncomputable def primaryKernelEquiv (f : Module.End K V) (p : K[X])
    (hp : p ≠ 0) (hAnn : p.eval₂ (Module.toModuleEnd K V) f = 0) :
    V ≃ₗ[K] (∀ q : (normalizedFactors p).toFinset,
      LinearMap.ker ((eval₂ (Module.toModuleEnd K V) f (q : K[X])) ^
        (normalizedFactors p).count (q : K[X]))) := by
  classical
  let σ : K →+* Module.End K V := Module.toModuleEnd K V
  have hcomm : ∀ a, Commute (σ a) f := by
    intro a
    apply LinearMap.ext
    intro v
    change a • f v = f (a • v)
    exact (f.map_smul a v).symm
  let Φ := eval₂RingHom' σ f hcomm
  let m := normalizedFactors p
  have hfactor (q : m.toFinset) :
      Irreducible (q : K[X]) ∧ (q : K[X]).Monic ∧ (q : K[X]) ∣ p := by
    exact (Polynomial.mem_normalizedFactors_iff hp).mp
      (Multiset.mem_toFinset.mp q.property)
  have hcopPow : Pairwise fun q r : m.toFinset ↦
      IsCoprime ((q : K[X]) ^ m.count (q : K[X]))
        ((r : K[X]) ^ m.count (r : K[X])) := by
    intro q r hqr
    apply IsCoprime.pow
    apply (hfactor q).1.coprime_iff_not_dvd.mpr
    intro hdvd
    apply hqr
    apply Subtype.ext
    exact eq_of_monic_of_associated (hfactor q).2.1 (hfactor r).2.1
      ((hfactor q).1.associated_of_dvd (hfactor r).1 hdvd)
  have hprod : m.prod = ∏ q : m.toFinset, (q : K[X]) ^ m.count (q : K[X]) := by
    calc
      m.prod = ∏ q ∈ m.toFinset, q ^ m.count q := Finset.prod_multiset_count m
      _ = ∏ q : m.toFinset, (q : K[X]) ^ m.count (q : K[X]) :=
        (Finset.prod_coe_sort m.toFinset (fun q : K[X] ↦ q ^ m.count q)).symm
  have hunit : IsUnit (Φ (C p.leadingCoeff)) :=
    ((IsUnit.mk0 p.leadingCoeff (leadingCoeff_ne_zero.mpr hp)).map
      (C : K →+* K[X])).map Φ
  have hAnnFactors : Φ m.prod = 0 := by
    apply hunit.mul_right_eq_zero.mp
    rw [← map_mul]
    change Φ (C p.leadingCoeff * (normalizedFactors p).prod) = 0
    rw [leadingCoeff_mul_prod_normalizedFactors]
    exact hAnn
  have hAnnProd : Φ (∏ q : m.toFinset, (q : K[X]) ^ m.count (q : K[X])) = 0 := by
    rw [← hprod]
    exact hAnnFactors
  have hEvalPow (q : K[X]) (n : ℕ) :
      eval₂RingHom' σ f hcomm (q ^ n) =
        (eval₂ (Module.toModuleEnd K V) f q) ^ n := by
    simpa only [eval₂RingHom'_apply, σ] using
      (map_pow (eval₂RingHom' σ f hcomm) q n)
  -- Transport equal kernel submodules before coercing them to their carrier types.
  exact
    (Polynomial.linearEquivPiKer σ f hcomm
      (fun q : m.toFinset ↦ (q : K[X]) ^ m.count (q : K[X])) hcopPow hAnnProd).trans
      (LinearEquiv.piCongrRight fun q : m.toFinset ↦
        LinearEquiv.ofEq _ _
          (congrArg (fun g : Module.End K V ↦ LinearMap.ker g)
            (hEvalPow (q : K[X]) (m.count (q : K[X])))))
