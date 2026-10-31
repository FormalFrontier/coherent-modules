/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Noetherian
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Noetherian modules under essentially finite-type scalar extension

For an essentially finite-type algebra of commutative rings `R → S`, extension of
scalars sends every Noetherian `R`-module `M` to a Noetherian `S`-module
`S ⊗[R] M`. Neither scalar ring is assumed Noetherian.

The proof passes to the annihilator quotients of `M` and its scalar extension.
The tensor-annihilator containment is proved for semirings; no flatness is used.

## References

The coefficient-annihilator reduction follows the scalar-extension argument of
Formal Frontier Agents. The proof reuses this library's
`isNoetherianRing_quotient_annihilator`, following the formalization in Adic Modules,
and Mathlib's base-change finiteness, quotient module actions, essentially
finite-type Noetherian ascent and bijective semilinear invariance.
-/

@[expose] public section

universe uR uS uM

open scoped TensorProduct

/-- Every scalar annihilating a module annihilates its scalar extension, with
scalars acting on the left tensor factor. No finiteness or flatness is required. -/
theorem TensorProduct.annihilator_le_comap_annihilator
    (R : Type uR) (S : Type uS) (M : Type uM)
    [CommSemiring R] [Semiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M] :
    Module.annihilator R M ≤
      (Module.annihilator S (S ⊗[R] M)).comap (algebraMap R S) := by
  intro r hr
  apply Ideal.mem_comap.mpr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul,
      TensorProduct.smul_tmul, Module.mem_annihilator.mp hr m, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- Extension of scalars along an essentially finite-type algebra of commutative
rings preserves Noetherian modules. The tensor has its canonical left-factor
scalar action; neither ambient ring is assumed Noetherian. -/
theorem Algebra.EssFiniteType.isNoetherian_tensorProduct
    (R : Type uR) (S : Type uS) (M : Type uM)
    [CommRing R] [CommRing S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [Algebra.EssFiniteType R S] [IsNoetherian R M] :
    IsNoetherian S (S ⊗[R] M) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let N := S ⊗[R] M
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup S
  let I := Module.annihilator R M
  let L := Module.annihilator S N
  let B := R ⧸ I
  let C := S ⧸ L
  have h : I ≤ L.comap (algebraMap R S) :=
    TensorProduct.annihilator_le_comap_annihilator R S M
  let : Algebra B C := Ideal.Quotient.algebraQuotientOfLEComap h
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.quotientMap_mk (H := h) (x := r)).symm
  let : IsNoetherianRing B := isNoetherianRing_quotient_annihilator M
  let : Algebra.EssFiniteType R C := inferInstance
  let : Algebra.EssFiniteType B C := Algebra.EssFiniteType.of_comp R B C
  let : IsNoetherianRing C := Algebra.EssFiniteType.isNoetherianRing B C
  let : Module C N := Module.quotientAnnihilator (R := S) (M := N)
  let f : N →ₛₗ[Ideal.Quotient.mk L] N :=
    (Module.isTorsionBySet_annihilator S N).semilinearMap
  have : Module.Finite S N := Module.Finite.base_change R S M
  have : Module.Finite C N := Module.Finite.of_surjective f Function.surjective_id
  exact (LinearMap.isNoetherian_iff_of_bijective f Function.bijective_id).mpr inferInstance
