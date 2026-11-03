/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Polynomial evaluation and evaluation on generating families

An additive map intertwining two coefficient representations and two endomorphisms also intertwines
polynomial evaluation. The coefficient semiring need not be commutative, and represented elements
need not commute with the selected endomorphism. The semilinear specialization is expressed as an
equality of compositions, without a module structure on the space of semilinear maps.

The canonical hom `Module.toAddMonoidEnd (Module.End R M) M` forgets linearity of endomorphisms.
`Polynomial.hom_eval₂` transports evaluation through this hom. Specializing polynomial intertwining
to a power of `X` gives the power-intertwining relation of
`Module.End.commute_pow_left_of_commute`. On regular semimodules, left-multiplication
representations and evaluation at `1` give the represented form of `Polynomial.hom_eval₂`.

Separately, semilinear maps out of a finitely generated semimodule are determined by their values on
a finite spanning family. When the scalar actions on the codomain commute, evaluation on such a
family is a linear injection into a finite product of the codomain. This map is assembled from
`LinearMap.pi`, `LinearMap.flip`, and `LinearMap.id`; its coordinate at `i` sends `f` to `f (v i)`.
-/

@[expose] public section

universe uR uR₂ uS uM uN

/-- Pointwise finite sums with the summands kept in the endomorphism type. -/
private theorem addMonoidEnd_finsetSum_apply
    {ι : Type*} {A : Type*} [AddCommMonoid A]
    (f : ι → AddMonoid.End A) (s : Finset ι) (a : A) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a :=
  AddMonoidHom.finsetSum_apply (f : ι → A →+ A) s a

namespace Polynomial

/-- An additive map intertwining the coefficient representations and the selected endomorphisms
intertwines their polynomial evaluations. Neither commutativity of the coefficient semiring nor
commutation of its image with the endomorphism is required. -/
theorem semiconj_eval₂
    {S : Type uS} [Semiring S]
    {M : Type uM} {N : Type uN} [AddCommMonoid M] [AddCommMonoid N]
    (h : M →+ N)
    (σ : S →+* AddMonoid.End M) (τ : S →+* AddMonoid.End N)
    (f : AddMonoid.End M) (g : AddMonoid.End N)
    (hcoeff : ∀ s, Function.Semiconj h (σ s) (τ s))
    (hfg : Function.Semiconj h f g) (p : Polynomial S) :
    Function.Semiconj h
      (p.eval₂ σ f : AddMonoid.End M) (p.eval₂ τ g : AddMonoid.End N) := by
  classical
  have hpow (i : ℕ) :
      Function.Semiconj h (f ^ i : AddMonoid.End M) (g ^ i : AddMonoid.End N) := by
    simpa only [AddMonoid.End.coe_pow] using hfg.iterate_right i
  have hterm (i : ℕ) (s : S) (m : M) :
      h ((σ s * f ^ i : AddMonoid.End M) m) =
        (τ s * g ^ i : AddMonoid.End N) (h m) := by
    simpa only [AddMonoid.End.coe_mul, Function.comp_apply] using
      (hcoeff s ((f ^ i : AddMonoid.End M) m)).trans
        (congrArg (τ s) (hpow i m))
  intro m
  -- Plain evaluation keeps the coefficient on the left; no factors are exchanged.
  simp only [eval₂_eq_sum, Polynomial.sum]
  rw [addMonoidEnd_finsetSum_apply, addMonoidEnd_finsetSum_apply, _root_.map_sum]
  exact Finset.sum_congr rfl fun i (_ : i ∈ p.support) ↦ hterm i (p.coeff i) m

end Polynomial

namespace LinearMap

/-- Polynomial evaluation respects a coefficient-compatible semilinear intertwiner, even when the
source and target scalar semirings differ. The canonical homs
`Module.toAddMonoidEnd (Module.End R M) M` and `Module.toAddMonoidEnd (Module.End R₂ N) N`
identify these evaluations with evaluations in additive endomorphisms via `Polynomial.hom_eval₂`.
No coefficient/end commutation hypothesis is needed for `Polynomial.eval₂`. -/
theorem eval₂_comp
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS} [Semiring R] [Semiring R₂] [Semiring S]
    {M : Type uM} {N : Type uN} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R₂ N] {η : R →+* R₂} (h : M →ₛₗ[η] N)
    (σ : S →+* Module.End R M) (τ : S →+* Module.End R₂ N)
    (f : Module.End R M) (g : Module.End R₂ N)
    (hcoeff : ∀ s, (τ s).comp h = h.comp (σ s))
    (hfg : g.comp h = h.comp f) (p : Polynomial S) :
    (p.eval₂ τ g).comp h = h.comp (p.eval₂ σ f) := by
  let Fₘ := Module.toAddMonoidEnd (Module.End R M) M
  let Fₙ := Module.toAddMonoidEnd (Module.End R₂ N) N
  have heval := Polynomial.semiconj_eval₂ h.toAddMonoidHom
    (Fₘ.comp σ) (Fₙ.comp τ) (Fₘ f) (Fₙ g)
    (fun s m ↦ (LinearMap.congr_fun (hcoeff s) m).symm)
    (fun m ↦ (LinearMap.congr_fun hfg m).symm) p
  rw [← Polynomial.hom_eval₂ p σ Fₘ f, ← Polynomial.hom_eval₂ p τ Fₙ g] at heval
  ext m
  exact (heval m).symm

/-- A finitely generated semimodule has a finite spanning family and a bundled injective linear
map given by evaluation of semilinear maps on that family. -/
theorem exists_fin_injective_eval
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring R₂] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R₂ N] [Module S N] (σ : R →+* R₂)
    [SMulCommClass R₂ S N] [Module.Finite R M] :
    ∃ (n : ℕ) (v : Fin n → M) (e : (M →ₛₗ[σ] N) →ₗ[S] (Fin n → N)),
      Submodule.span R (Set.range v) = ⊤ ∧
        (∀ f i, e f i = f (v i)) ∧ Function.Injective e := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨n, v, LinearMap.pi (fun i ↦
    (LinearMap.flip (LinearMap.id : (M →ₛₗ[σ] N) →ₗ[S] (M →ₛₗ[σ] N))) (v i)), hv, ?_, ?_⟩
  · intro f i
    simp only [LinearMap.pi_apply, LinearMap.flip_apply, LinearMap.id_apply]
  · intro f g h
    exact LinearMap.ext_on_range hv fun i ↦ by
      simpa only [LinearMap.pi_apply, LinearMap.flip_apply, LinearMap.id_apply] using congrFun h i

end LinearMap
