/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents
-/
module

public import CoherentModules.Basic
public import CoherentModules.FinitePresentation
public import CoherentModules.LinearAlgebra.Finsupp.LSum
public import CoherentModules.LinearAlgebra.LinearMap.Exact

/-!
# Semilinear maps into coherent modules

This file proves that semilinear maps from a finitely presented module into a coherent module
form a coherent module for a commuting scalar action on the target. The source and target scalar
semirings, the acting ring, and the two module carriers have independent universes. All module
structures are the given ones; the Hom module has the pointwise action on the target.

## Main declarations

* `Module.IsCoherent.semilinearMap`: coherence of a semilinear-map module over an arbitrary
  scalar homomorphism, with a finitely presented group source and a coherent group target.
* `Module.IsCoherent.linearMap`: the same-base commutative-ring specialization.

## Implementation notes

The finite-free presentation is used contravariantly through semilinear Hom. Both finite-free
Hom modules are coherent by finite products, so the kernel is coherent. No additive group
structure on the finite free source semimodules is required.

## References and credit

The proof uses Mathlib's finite-presentation, semilinear precomposition and linear-equivalence
APIs, together with its finite-product and free-semimodule constructions. The finite-free Hom
comparison extends Mathlib's `LinearEquiv.piRing`, using the semilinear free-module equivalence
built from Johannes Hölzl's `Finsupp.lsum` and the bilinear-map formalization by Kenny Lau and
Mario Carneiro.
-/

@[expose] public section

universe uR uR₂ uS uM uN

namespace Module.IsCoherent

section FiniteHom

variable {R : Type uR} {R₂ : Type uR₂} {S : Type uS} {N : Type uN}
variable [Semiring R] [Semiring R₂] [Semiring S] [AddCommMonoid N]
variable [Module R₂ N] [Module S N] [SMulCommClass R₂ S N]

private noncomputable def finiteHomEquiv (σ : R →+* R₂) (k : ℕ) :
    (Fin k → N) ≃ₗ[S] ((Fin k → R) →ₛₗ[σ] N) := by
  classical
  let e := Finsupp.linearEquivFunOnFinite R R (Fin k)
  let A : ((Fin k →₀ R) →ₛₗ[σ] N) →ₗ[S] ((Fin k → R) →ₛₗ[σ] N) :=
    LinearMap.lcompₛₗ (σ₁₃ := σ) S N σ e.symm.toLinearMap
  let B : ((Fin k → R) →ₛₗ[σ] N) →ₗ[S] ((Fin k →₀ R) →ₛₗ[σ] N) :=
    LinearMap.lcompₛₗ (σ₁₃ := σ) S N σ e.toLinearMap
  have hAB : A.comp B = LinearMap.id (R := S) (M := (Fin k → R) →ₛₗ[σ] N) := by
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro x
    simp only [A, B, LinearMap.comp_apply, LinearMap.lcompₛₗ_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  have hBA : B.comp A = LinearMap.id (R := S) (M := (Fin k →₀ R) →ₛₗ[σ] N) := by
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro d
    simp only [A, B, LinearMap.comp_apply, LinearMap.lcompₛₗ_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, LinearMap.id_apply]
  let eHom : ((Fin k →₀ R) →ₛₗ[σ] N) ≃ₗ[S] ((Fin k → R) →ₛₗ[σ] N) :=
    LinearEquiv.ofLinearMap A B hAB hBA
  exact (Finsupp.lliftₛₗ N R S (Fin k) σ).trans eHom

private theorem finiteHomEquiv_symm_apply (σ : R →+* R₂) (k : ℕ)
    (f : (Fin k → R) →ₛₗ[σ] N) (i : Fin k) :
    (finiteHomEquiv (S := S) σ k).symm f i = f (Pi.single i 1) := by
  classical
  simp only [finiteHomEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_ofLinearMap,
    LinearEquiv.coe_ofLinearMap, Finsupp.lliftₛₗ_symm_apply, LinearMap.lcompₛₗ_apply,
    LinearEquiv.coe_toLinearMap, Finsupp.linearEquivFunOnFinite_single]

end FiniteHom

section LinearComparison

variable {R : Type uR} {S : Type uS} {N : Type uN}
variable [Semiring R] [Semiring S] [AddCommMonoid N]
variable [Module R N] [Module S N] [SMulCommClass R S N]

private theorem finiteHomEquiv_id (k : ℕ) :
    finiteHomEquiv (S := S) (N := N) (RingHom.id R) k =
      (LinearEquiv.piRing R N (Fin k) S).symm := by
  let q := finiteHomEquiv (S := S) (N := N) (RingHom.id R) k
  let p := LinearEquiv.piRing R N (Fin k) S
  apply LinearEquiv.ext
  intro a
  apply p.injective
  calc
    p (q a) = q.symm (q a) := by
      funext i
      simpa only [p, LinearEquiv.piRing_apply] using
        (finiteHomEquiv_symm_apply (S := S) (RingHom.id R) k (q a) i).symm
    _ = a := q.symm_apply_apply a
    _ = p (p.symm a) := (p.apply_symm_apply a).symm

end LinearComparison

/-- Semilinear maps from a finitely presented group module into a coherent group module form
a coherent module for the given commuting action of `S` on the target.

The two scalar semirings and the acting ring may be noncommutative. No `S`-action on the source,
`R`-action on the target, or surjectivity of the scalar homomorphism is required. The Hom action
is the original pointwise `S`-action, and all five universes are independent. -/
theorem semilinearMap
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS}
    {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring R₂] [Ring S]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R₂ N] [Module S N]
    (σ : R →+* R₂) [SMulCommClass R₂ S N]
    [Module.FinitePresentation R M] [Module.IsCoherent S N] :
    Module.IsCoherent S (M →ₛₗ[σ] N) := by
  classical
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin_exact R M
  let _ : Module.IsCoherent S (Fin n → N) := Module.IsCoherent.pi
  let _ : Module.IsCoherent S (Fin m → N) := Module.IsCoherent.pi
  let _ : Module.IsCoherent S ((Fin n → R) →ₛₗ[σ] N) :=
    Module.IsCoherent.of_equiv (finiteHomEquiv (S := S) σ n)
  let _ : Module.IsCoherent S ((Fin m → R) →ₛₗ[σ] N) :=
    Module.IsCoherent.of_equiv (finiteHomEquiv (S := S) σ m)
  let gStar : (M →ₛₗ[σ] N) →ₗ[S] ((Fin n → R) →ₛₗ[σ] N) :=
    LinearMap.lcompₛₗ (σ₁₃ := σ) S N σ g
  let fStar : ((Fin n → R) →ₛₗ[σ] N) →ₗ[S] ((Fin m → R) →ₛₗ[σ] N) :=
    LinearMap.lcompₛₗ (σ₁₃ := σ) S N σ f
  have hInj : Function.Injective gStar := hg.injective_linearMapComp_right
  have hStar : Function.Exact gStar fStar :=
    LinearMap.exact_lcompₛₗ_of_exact_of_surjective
      (R₂ := R₂) (S := S) (N := N) σ hfg hg
  have hEq : LinearMap.range gStar = LinearMap.ker fStar :=
    (LinearMap.exact_iff.mp hStar).symm
  let _ : Module.IsCoherent S (LinearMap.ker fStar) := Module.IsCoherent.ker fStar
  let e : (M →ₛₗ[σ] N) ≃ₗ[S] LinearMap.ker fStar :=
    (LinearEquiv.ofInjective gStar hInj).trans
      (LinearEquiv.ofEq (LinearMap.range gStar) (LinearMap.ker fStar) hEq)
  exact Module.IsCoherent.of_equiv e.symm

end Module.IsCoherent

universe u v w

namespace Module.IsCoherent

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Linear maps from a finitely presented module into a coherent module form a coherent module. -/
theorem linearMap [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M →ₗ[R] N) :=
  Module.IsCoherent.semilinearMap (R₂ := R) (S := R) (M := M) (N := N) (RingHom.id R)

end Module.IsCoherent
