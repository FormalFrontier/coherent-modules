/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicKrull
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite presentation and adic quotients

For a finitely generated module over a commutative ring, full submodule adic
cofinality and containment of the ideal in the Jacobson radical allow finite
presentation to be detected on all positive adic quotients. Finite presentation
of each quotient is taken over the corresponding quotient ring.

The relation submodule in a finite free cover is not assumed finitely generated.
Adic cofinality compares a sufficiently deep induced filtration with its
intrinsic first adic layer; finite generation of that layer then detects finite
generation of the relation submodule.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5 (2017), Corollary 0.7.4.19.
-/

@[expose] public section

open scoped Pointwise
open scoped Ideal.Quotient

universe uR uM uF

namespace Ideal

variable {R : Type uR} [CommRing R]

/-- A finite presentation after reduction makes the intrinsic quotient of a
relation submodule finite whenever the induced denominator lies in that
intrinsic denominator. -/
private theorem finite_quotient_ker_of_reduction
    {F : Type uF} [AddCommGroup F] [Module R F] [Module.Finite R F]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (I J : Ideal R) (f : F →ₗ[R] M) (hf : Function.Surjective f)
    [Module.FinitePresentation (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))]
    (hcut : f.ker ⊓ (J • (⊤ : Submodule R F)) ≤ I • f.ker) :
    Module.Finite R (f.ker ⧸ (I • (⊤ : Submodule R f.ker))) := by
  let A : Submodule R F := J • ⊤
  let B : Submodule R M := J • ⊤
  have hmap : A.map f = B := by
    dsimp [A, B]
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  have hAB : A ≤ B.comap f :=
    Submodule.map_le_iff_le_comap.mp hmap.le
  let gR : F ⧸ A →ₗ[R] M ⧸ B := A.mapQ B f hAB
  let g : F ⧸ A →ₗ[R ⧸ J] M ⧸ B :=
    LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective) gR
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨m, rfl⟩ := B.mkQ_surjective y
    obtain ⟨x, rfl⟩ := hf m
    exact ⟨A.mkQ x, rfl⟩
  let : Module.Finite (R ⧸ J) (F ⧸ A) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ J) (F ⧸ A)
  let : Module.Finite (R ⧸ J) g.ker :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker g hg)
  let : Module.Finite R g.ker := Module.Finite.trans (R ⧸ J) g.ker
  let q : f.ker →ₗ[R] g.ker :=
    { toFun := fun x => ⟨A.mkQ (x : F), by
        change B.mkQ (f x) = 0
        rw [show f x = 0 from x.property, map_zero]⟩
      map_add' := fun x y => Subtype.ext (A.mkQ.map_add (x : F) (y : F))
      map_smul' := fun r x => Subtype.ext (A.mkQ.map_smul r (x : F)) }
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := A.mkQ_surjective (y : F ⧸ A)
    have hfx : f x ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change g (A.mkQ x) = 0
      rw [hx]
      exact y.property
    rw [← hmap] at hfx
    obtain ⟨z, hz, hzx⟩ := hfx
    let k : f.ker := ⟨x - z, by
      change f (x - z) = 0
      rw [map_sub, hzx, sub_self]⟩
    refine ⟨k, Subtype.ext ?_⟩
    change A.mkQ (x - z) = (y : F ⧸ A)
    have hz0 : A.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero A).mpr hz
    rw [map_sub, hz0, sub_zero, hx]
  have hqker : q.ker ≤ I • (⊤ : Submodule R f.ker) := by
    intro x hx
    change q x = 0 at hx
    have hx0 : A.mkQ (x : F) = 0 := congrArg Subtype.val hx
    have hxA : (x : F) ∈ A := (Submodule.Quotient.mk_eq_zero A).mp hx0
    have hxI : (x : F) ∈ I • f.ker := hcut ⟨x.property, hxA⟩
    have hsmul : (I • (⊤ : Submodule R f.ker)).map f.ker.subtype = I • f.ker := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [← hsmul] at hxI
    obtain ⟨z, hz, hzx⟩ := hxI
    exact (show z = x from Subtype.ext hzx) ▸ hz
  let e := q.quotKerEquivOfSurjective hq
  let : Module.Finite R (f.ker ⧸ q.ker) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let t : f.ker ⧸ q.ker →ₗ[R] f.ker ⧸ (I • (⊤ : Submodule R f.ker)) :=
    q.ker.liftQ (I • (⊤ : Submodule R f.ker)).mkQ (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hqker hx))
  apply Module.Finite.of_surjective t
  intro y
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R f.ker)).mkQ_surjective y
  exact ⟨q.ker.mkQ x, rfl⟩

/-- Under full adic cofinality and the Jacobson radical condition, finite
presentation of all positive adic quotients implies finite presentation of a
finite module. This is the reverse implication of Fujiwara--Kato,
*Foundations of Rigid Geometry I*, Corollary 0.7.4.19. -/
private theorem finitePresentation_of_forall_quotient_pow_smul
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hAP : I.HasSubmoduleAdicCofinality) (hJ : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (hQ : ∀ n : ℕ, 0 < n →
      Module.FinitePresentation (R ⧸ I ^ n)
        (M ⧸ ((I ^ n) • (⊤ : Submodule R M)))) :
    Module.FinitePresentation R M := by
  obtain ⟨b, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨m, hm⟩ := hAP.cofinal f.ker 1
  have hpow : I ^ (m + 1) ≤ I ^ m := by
    rw [pow_succ]
    exact Ideal.mul_le_left
  have hcut : f.ker ⊓ ((I ^ (m + 1)) • (⊤ : Submodule R (Fin b → R))) ≤
      I • f.ker := by
    intro x hx
    apply (show f.ker ⊓ ((I ^ m) • (⊤ : Submodule R (Fin b → R))) ≤ I • f.ker
      from by simpa only [pow_one] using hm)
    exact ⟨hx.1, Submodule.smul_mono hpow le_rfl hx.2⟩
  let : Module.FinitePresentation (R ⧸ I ^ (m + 1))
      (M ⧸ ((I ^ (m + 1)) • (⊤ : Submodule R M))) :=
    hQ (m + 1) (Nat.zero_lt_succ m)
  have hfinite : Module.Finite R (f.ker ⧸ (I • (⊤ : Submodule R f.ker))) :=
    finite_quotient_ker_of_reduction I (I ^ (m + 1)) f hf hcut
  have hJac : I ≤ (Module.annihilator R (Fin b → R)).jacobson :=
    hJ.trans (Ideal.jacobson_mono bot_le)
  have hfg : f.ker.FG :=
    Submodule.fg_of_finite_quotient_smul (I := I) f.ker
      hAP.hasFiniteSubmoduleAdicCofinality hJac hfinite
  exact (Module.FinitePresentation.fg_ker_iff f hf).mp hfg

/-- A finite module is finitely presented if and only if every positive adic
quotient is finitely presented over its quotient ring, under full submodule
adic cofinality and the Jacobson radical condition. This is Corollary 0.7.4.19
of Fujiwara--Kato, *Foundations of Rigid Geometry I*. -/
theorem finitePresentation_iff_forall_quotient_pow_smul
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hAP : I.HasSubmoduleAdicCofinality) (hJ : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    Module.FinitePresentation R M ↔
      ∀ n : ℕ, 0 < n →
        Module.FinitePresentation (R ⧸ I ^ n)
          (M ⧸ ((I ^ n) • (⊤ : Submodule R M))) := by
  constructor
  · intro hM n _
    let : Module.FinitePresentation R M := hM
    let e := LinearEquiv.extendScalarsOfSurjective
      (R := R) (S := R ⧸ I ^ n)
      (Ideal.Quotient.mk_surjective (I := I ^ n))
      (TensorProduct.quotTensorEquivQuotSMul M (I ^ n))
    exact Module.FinitePresentation.of_equiv e
  · exact finitePresentation_of_forall_quotient_pow_smul I M hAP hJ

end Ideal
