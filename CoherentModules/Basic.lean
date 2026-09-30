/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor and other Formal Frontier AI agents
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Coherent modules and rings

This file introduces coherent modules and rings and proves their elementary
closure properties. A module is coherent when it is finitely generated and all
of its finitely generated submodules are finitely presented.

## Main declarations

* `Module.IsCoherent`: coherent modules.
* `Module.IsCoherent.iff_finite_and_fg_ker`: characterization by kernels of maps from
  finite-rank free modules.
* `Module.IsCoherent.of_exact`: coherence of the middle term of a short exact sequence.
* `IsCoherentRing`: coherent rings.
-/

@[expose] public section

universe u v w x

namespace Module

section Ring

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- A module is coherent if it is finitely generated and every finitely
generated submodule is finitely presented. -/
class IsCoherent : Prop where
  finite : Module.Finite R M
  finitePresentation_submodule :
    ∀ (N : Submodule R M), N.FG → Module.FinitePresentation R N

variable {R M}

instance IsCoherent.toFinite [Module.IsCoherent R M] : Module.Finite R M :=
  IsCoherent.finite

/-- Every coherent module is finitely presented. -/
instance IsCoherent.toFinitePresentation [Module.IsCoherent R M] :
    Module.FinitePresentation R M := by
  let _ : Module.FinitePresentation R (⊤ : Submodule R M) :=
    IsCoherent.finitePresentation_submodule ⊤ Module.Finite.fg_top
  exact Module.FinitePresentation.of_equiv Submodule.topEquiv

/-- A module is coherent exactly when it is finite and the kernel of every linear map from a
finite-rank free module is finitely generated. -/
theorem IsCoherent.iff_finite_and_fg_ker :
    Module.IsCoherent R M ↔
      Module.Finite R M ∧
        ∀ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), (LinearMap.ker f).FG := by
  constructor
  · intro h
    let _ : Module.IsCoherent R M := h
    refine ⟨inferInstance, ?_⟩
    intro n f
    let _ : Module.FinitePresentation R (LinearMap.range f) :=
      IsCoherent.finitePresentation_submodule _ (Submodule.fg_range f)
    simpa only [LinearMap.ker_rangeRestrict] using
      Module.FinitePresentation.fg_ker f.rangeRestrict
        (LinearMap.surjective_rangeRestrict f)
  · rintro ⟨hM, hker⟩
    exact
      { finite := hM
        finitePresentation_submodule := fun N hN ↦ by
          let _ : Module.Finite R N := Module.Finite.of_fg hN
          obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
          have hfg : (LinearMap.ker (N.subtype ∘ₗ f)).FG := hker n (N.subtype ∘ₗ f)
          rw [LinearMap.ker_comp_of_ker_eq_bot f (Submodule.ker_subtype N)] at hfg
          exact Module.finitePresentation_of_surjective f hf hfg }

/-- A finitely generated submodule of a coherent module is coherent. -/
theorem IsCoherent.submodule [Module.IsCoherent R M] (N : Submodule R M) (hN : N.FG) :
    Module.IsCoherent R N where
  finite := Module.Finite.of_fg hN
  finitePresentation_submodule P hP := by
    let f : P →ₗ[R] M := N.subtype ∘ₗ P.subtype
    have hf : Function.Injective f :=
      (Submodule.injective_subtype N).comp (Submodule.injective_subtype P)
    let _ : Module.Finite R P := Module.Finite.of_fg hP
    have hrange : (LinearMap.range f).FG := Submodule.fg_range f
    let _ : Module.FinitePresentation R (LinearMap.range f) :=
      IsCoherent.finitePresentation_submodule _ hrange
    exact Module.FinitePresentation.of_equiv (LinearEquiv.ofInjective f hf).symm

/-- The range of a linear map from a finite module into a coherent module is coherent. -/
theorem IsCoherent.range {N : Type w} [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.range f) :=
  IsCoherent.submodule _ (Submodule.fg_range f)

/-- In a short exact sequence of modules, if the outer modules are coherent, then so is the
middle module. -/
theorem IsCoherent.of_exact {N : Type w} {P : Type x}
    [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
    [Module.IsCoherent R M] [Module.IsCoherent R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.IsCoherent R N where
  finite := Module.Finite.of_exact h hg
  finitePresentation_submodule Q hQ := by
    let _ : Module.Finite R Q := Module.Finite.of_fg hQ
    let r : Q →ₗ[R] P := g ∘ₗ Q.subtype
    let I : Submodule R P := LinearMap.range r
    let q : Q →ₗ[R] I := r.rangeRestrict
    have hq : Function.Surjective q := LinearMap.surjective_rangeRestrict r
    have hI : I.FG := Submodule.fg_range r
    let _ : Module.IsCoherent R I := IsCoherent.submodule I hI
    have hker : (LinearMap.ker q).FG := Module.FinitePresentation.fg_ker q hq
    let _ : Module.Finite R (LinearMap.ker q) := Module.Finite.of_fg hker
    let j : LinearMap.ker q →ₗ[R] N := Q.subtype ∘ₗ (LinearMap.ker q).subtype
    have hj : ∀ z, j z ∈ LinearMap.range f := by
      intro z
      rw [← h.linearMap_ker_eq]
      have hz := congrArg Subtype.val z.2
      change r z.1 = 0 at hz
      simpa [j, r] using hz
    let k : LinearMap.ker q →ₗ[R] M :=
      (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
        j.codRestrict (LinearMap.range f) hj
    have hk : Function.Injective k := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa [k, j] using congrArg f hab
    let _ : Module.IsCoherent R (LinearMap.range k) := IsCoherent.range k
    let _ : Module.FinitePresentation R (LinearMap.ker q) :=
      Module.FinitePresentation.of_equiv (R := R) (M := LinearMap.range k)
        (N := LinearMap.ker q) (LinearEquiv.ofInjective k hk).symm
    exact Module.finitePresentation_of_ker q hq

/-- The kernel of a linear map between coherent modules is coherent. -/
theorem IsCoherent.ker {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.ker f) := by
  let _ : Module.IsCoherent R (LinearMap.range f) := IsCoherent.range f
  have hker : (LinearMap.ker f.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker f.rangeRestrict
      (LinearMap.surjective_rangeRestrict f)
  rw [LinearMap.ker_rangeRestrict] at hker
  exact IsCoherent.submodule _ hker

/-- The kernel of a linear map between coherent modules is finitely presented. -/
theorem IsCoherent.finitePresentation_ker {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.FinitePresentation R (LinearMap.ker f) := by
  let _ : Module.IsCoherent R (LinearMap.ker f) := IsCoherent.ker f
  infer_instance

/-- The quotient of a coherent module by a finitely generated submodule is coherent. -/
theorem IsCoherent.quotient [Module.IsCoherent R M] (N : Submodule R M) (hN : N.FG) :
    Module.IsCoherent R (M ⧸ N) where
  finite := inferInstance
  finitePresentation_submodule P hP := by
    let Q : Submodule R M := P.comap N.mkQ
    have hNQ : N ≤ Q := by
      intro x hx
      change N.mkQ x ∈ P
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hx]
      exact P.zero_mem
    have hQ : Q.FG := by
      apply Submodule.fg_of_fg_map_of_fg_inf_ker N.mkQ
      · rw [Submodule.map_comap_eq_of_surjective N.mkQ_surjective P]
        exact hP
      · rw [Submodule.ker_mkQ, inf_eq_right.mpr hNQ]
        exact hN
    let _ : Module.IsCoherent R Q := IsCoherent.submodule Q hQ
    let f : Q →ₗ[R] P := N.mkQ.restrict fun x hx ↦ hx
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := N.mkQ_surjective y.1
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      change N.mkQ x ∈ P
      rw [hx]
      exact y.2
    apply Module.finitePresentation_of_surjective f hf
    rw [LinearMap.ker_restrict, Submodule.ker_mkQ, ← Submodule.range_inclusion N Q hNQ]
    let _ : Module.Finite R N := Module.Finite.of_fg hN
    exact Submodule.fg_range (Submodule.inclusion hNQ)

/-- The cokernel of a linear map between coherent modules is coherent. -/
theorem IsCoherent.cokernel {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (N ⧸ LinearMap.range f) :=
  IsCoherent.quotient _ (Submodule.fg_range f)

/-- Coherence is preserved by linear equivalence. -/
theorem IsCoherent.of_equiv {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsCoherent R M] (e : M ≃ₗ[R] N) : Module.IsCoherent R N where
  finite := Module.Finite.equiv e
  finitePresentation_submodule P hP := by
    let f : P →ₗ[R] M := e.symm.toLinearMap ∘ₗ P.subtype
    have hf : Function.Injective f := e.symm.injective.comp (Submodule.injective_subtype P)
    let _ : Module.Finite R P := Module.Finite.of_fg hP
    have hrange : (LinearMap.range f).FG := Submodule.fg_range f
    let _ : Module.FinitePresentation R (LinearMap.range f) :=
      IsCoherent.finitePresentation_submodule _ hrange
    exact Module.FinitePresentation.of_equiv (LinearEquiv.ofInjective f hf).symm

/-- Coherence is invariant under linear equivalence. -/
theorem IsCoherent.equiv_iff {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : Module.IsCoherent R M ↔ Module.IsCoherent R N :=
  ⟨fun _ ↦ IsCoherent.of_equiv e, fun _ ↦ IsCoherent.of_equiv e.symm⟩

/-- A subsingleton module is coherent. -/
instance (priority := 100) IsCoherent.of_subsingleton [Subsingleton M] :
    Module.IsCoherent R M where
  finite := inferInstance
  finitePresentation_submodule _ _ := inferInstance

/-- A finite module over a Noetherian ring is coherent. -/
instance (priority := 100) IsCoherent.of_isNoetherian [IsNoetherianRing R]
    [Module.Finite R M] : Module.IsCoherent R M where
  finite := inferInstance
  finitePresentation_submodule N hN := by
    let _ : Module.Finite R N := Module.Finite.of_fg hN
    exact Module.finitePresentation_of_finite R N

/-- The product of two coherent modules is coherent. -/
instance IsCoherent.prod {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] : Module.IsCoherent R (M × N) where
  finite := inferInstance
  finitePresentation_submodule P hP := by
    let _ : Module.Finite R P := Module.Finite.of_fg hP
    let f : P →ₗ[R] N := LinearMap.snd R M N ∘ₗ P.subtype
    let I : Submodule R N := LinearMap.range f
    let g : P →ₗ[R] I := f.rangeRestrict
    have hg : Function.Surjective g := LinearMap.surjective_rangeRestrict f
    have hI : I.FG := Submodule.fg_range f
    let _ : Module.FinitePresentation R I :=
      IsCoherent.finitePresentation_submodule I hI
    have hker : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g hg
    let k : LinearMap.ker g →ₗ[R] M :=
      LinearMap.fst R M N ∘ₗ P.subtype ∘ₗ (LinearMap.ker g).subtype
    have hk : Function.Injective k := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hxy
      · have hx : f x.1 = 0 := congrArg Subtype.val x.2
        have hy : f y.1 = 0 := congrArg Subtype.val y.2
        simpa [f] using hx.trans hy.symm
    let _ : Module.Finite R (LinearMap.ker g) := Module.Finite.of_fg hker
    have hrange : (LinearMap.range k).FG := Submodule.fg_range k
    let _ : Module.FinitePresentation R (LinearMap.range k) :=
      IsCoherent.finitePresentation_submodule _ hrange
    let _ : Module.FinitePresentation R (LinearMap.ker g) :=
      Module.FinitePresentation.of_equiv (R := R) (M := LinearMap.range k)
        (N := LinearMap.ker g) (LinearEquiv.ofInjective k hk).symm
    exact Module.finitePresentation_of_ker g hg

variable {I : Type*} [Finite I]

/-- A finite product of coherent modules is coherent. -/
instance IsCoherent.pi :
    ∀ {N : I → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
      [∀ i, Module.IsCoherent R (N i)], Module.IsCoherent R (∀ i, N i) := by
  apply Finite.induction_empty_option _ _ _ I
  · exact fun e h ↦ IsCoherent.of_equiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih ↦ IsCoherent.of_equiv (LinearEquiv.piOptionEquivProd R).symm

end Ring

end Module

section CoherentRing

variable (R : Type u) [Ring R]

/-- A ring is coherent when it is coherent as a module over itself. -/
class IsCoherentRing : Prop where
  coherent : Module.IsCoherent R R

instance IsCoherentRing.toIsCoherent [IsCoherentRing R] : Module.IsCoherent R R :=
  IsCoherentRing.coherent

/-- Every Noetherian ring is coherent. -/
instance (priority := 100) IsCoherentRing.of_isNoetherian [IsNoetherianRing R] :
    IsCoherentRing R :=
  ⟨inferInstance⟩

/-- A ring is coherent exactly when its finitely generated ideals are finitely presented. -/
theorem isCoherentRing_iff :
    IsCoherentRing R ↔ ∀ (I : Ideal R), I.FG → Module.FinitePresentation R I := by
  constructor
  · intro _ I hI
    exact Module.IsCoherent.finitePresentation_submodule I hI
  · intro h
    exact ⟨⟨inferInstance, h⟩⟩

/-- A finite free module over a coherent ring is coherent. -/
theorem Module.IsCoherent.of_free {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [IsCoherentRing R] : Module.IsCoherent R M := by
  let b := Module.Free.chooseBasis R M
  let _ := Module.Free.ChooseBasisIndex.fintype R M
  exact Module.IsCoherent.of_equiv b.equivFun.symm

/-- The kernel of a linear map between finite free modules over a coherent ring is
finitely presented. -/
theorem Module.finitePresentation_ker_of_free
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    [IsCoherentRing R] (f : M →ₗ[R] N) :
    Module.FinitePresentation R (LinearMap.ker f) := by
  let _ : Module.IsCoherent R M := Module.IsCoherent.of_free R
  let _ : Module.IsCoherent R N := Module.IsCoherent.of_free R
  exact Module.IsCoherent.finitePresentation_ker f

end CoherentRing
