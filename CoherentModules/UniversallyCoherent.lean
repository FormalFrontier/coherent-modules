/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor
-/
module

public import CoherentModules.Basic
public import CoherentModules.Localization
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Universally coherent rings

This file defines a commutative ring to be universally coherent when all of its finitely
presented commutative algebras are coherent. The target-algebra universe is a parameter of the
class: `IsUniversallyCoherent.{u, v} R` makes the assertion for algebras in `Type v`. This avoids
silently restricting the assertion to the universe containing `R`.

## Main declarations

* `IsUniversallyCoherent`: every finitely presented commutative algebra is coherent.
* `IsUniversallyCoherent.isCoherentRing_of_algEquiv`: transport along an algebra equivalence.
* `IsUniversallyCoherent.of_finitePresentation`: finitely presented algebra extensions preserve
  universal coherence, with independent base, extension and target universes.
* `IsUniversallyCoherent.polynomial`: polynomial rings over universally coherent rings are
  universally coherent.
* `IsUniversallyCoherent.of_isNoetherian`: Noetherian commutative rings are universally coherent.
* `IsUniversallyCoherent.of_forall_mvPolynomial`: coherence of all finite-variable polynomial
  rings implies universal coherence in any target universe.
* `IsUniversallyCoherent.iff_forall_mvPolynomial`: the finite-polynomial characterization at the
  base-ring universe.
* `IsUniversallyCoherent.changeTargetUniverse`: universal coherence in a target universe at
  least as large as the base-ring universe implies universal coherence in any target universe.
* `IsUniversallyCoherent.mvPolynomial`: polynomial rings in an arbitrary type of variables
  over a base-universe universally coherent ring are universally coherent in any target universe.
* `IsUniversallyCoherent.of_isLocalization`: arbitrary localizations of base-universe
  universally coherent rings are universally coherent in any target universe.

The finite-polynomial criterion reuses Mathlib's algebra finite-presentation quotient
characterization, together with coherent-module quotients and scalar-restriction transport.
Arbitrary-variable polynomial closure passes to finite-support charts, using Mathlib's
polynomial equivalences and monomial bases, flat kernel base change, and tensor-product
finiteness. The kernel comparison reuses work of Jingting Wang and Nailin Guan; tensor-product
finiteness reuses work of Kim Morrison and Johan Commelin.
Localization closure reuses coherent-module localization and Mathlib's polynomial-localization
instance.

## References

* Kazuhiro Fujiwara and Fumiharu Kato,
  [*Foundations of Rigid Geometry I*](https://arxiv.org/abs/1308.4734v5),
  arXiv:1308.4734v5 (2017-02-28), Chapter 0, §3.3, Definition 3.3.7 and its
  following paragraph (printed p. 104): the definition and finitely
  presented-algebra and localization closure of universal coherence.
  The finite-polynomial criterion here is a derived reformulation. Arbitrary-variable
  polynomial closure is a specialization of Exercise 0.3.3 (printed p. 105), not
  a formalization of its general filtered-colimit assertion.
-/

@[expose] public section

universe u v w

/-- A commutative ring is universally coherent (for target algebras in `Type v`) if every
finitely presented commutative algebra in that universe is a coherent ring.

At the base-ring target universe, this is the algebra-finite-presentation definition of
Fujiwara and Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5, Chapter 0,
Definition 3.3.7 (printed p. 104).

The target-algebra universe is deliberately independent of the universe containing the base
ring. Use `IsUniversallyCoherent.{u, v} R` when that universe is not inferred from an algebra.
For the source's ordinary fixed-universe meaning, use a target universe containing the base,
in particular `IsUniversallyCoherent.{u, u} R`. An unconstrained smaller target universe can
make the condition weaker. `changeTargetUniverse` passes from a target universe at least as
large as the base to every target universe; no smaller-target converse is asserted. -/
class IsUniversallyCoherent (R : Type u) [CommRing R] : Prop where
  isCoherentRing (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] : IsCoherentRing A

namespace IsUniversallyCoherent

/-- A universally coherent commutative ring is coherent as a ring. -/
instance toIsCoherentRing (R : Type u) [CommRing R] [IsUniversallyCoherent.{u, u} R] :
    IsCoherentRing R :=
  IsUniversallyCoherent.isCoherentRing R R

/-- Universal coherence gives coherence after replacing a finitely presented algebra by an
equivalent algebra, including when the two carrier types live in different universes. -/
theorem isCoherentRing_of_algEquiv (R : Type u) {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FinitePresentation R A] [IsUniversallyCoherent.{u, w} R]
    (e : A ≃ₐ[R] B) : IsCoherentRing B := by
  let _ : Algebra.FinitePresentation R B := Algebra.FinitePresentation.equiv e
  exact IsUniversallyCoherent.isCoherentRing R B

/-- A finitely presented commutative algebra over a universally coherent ring is universally
coherent, with independent base, extension and target universes.

Finite presentation here is as an algebra, not as a module. The proof uses
`Algebra.FinitePresentation.trans` for the composite algebra structure. -/
theorem of_finitePresentation (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [IsUniversallyCoherent.{u, w} R] : IsUniversallyCoherent.{v, w} S where
  isCoherentRing T := by
    intros
    let _ : Algebra R T := Algebra.compHom T (algebraMap R S)
    let _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : Algebra.FinitePresentation R T := Algebra.FinitePresentation.trans R S T
    exact IsUniversallyCoherent.isCoherentRing R T

/-- Polynomial rings over universally coherent rings are universally coherent, with the
same independently chosen target-algebra universe. -/
theorem polynomial (R : Type u) [CommRing R] [IsUniversallyCoherent.{u, w} R] :
    IsUniversallyCoherent.{u, w} (Polynomial R) :=
  of_finitePresentation R (Polynomial R)

/-- Every Noetherian commutative ring is universally coherent. -/
instance (priority := 100) of_isNoetherian (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCoherent.{u, v} R where
  isCoherentRing A := by
    intros
    let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    exact IsCoherentRing.of_isNoetherian A

universe uA uB

/-- Ring equivalences preserve coherence across independently sized carriers. -/
private theorem isCoherentRing_of_ringEquiv
    {A : Type uA} {B : Type uB} [Ring A] [Ring B]
    [IsCoherentRing A] (e : A ≃+* B) : IsCoherentRing B :=
  IsCoherentRing.of_ringEquiv e

/-- Coherence of every finite-variable polynomial ring implies universal coherence for
finitely presented algebras in any independently chosen target universe.

The proof uses `Algebra.FinitePresentation.iff` to present each target algebra as a quotient
by a finitely generated ideal, retaining its given algebra structure. -/
theorem of_forall_mvPolynomial (R : Type u) [CommRing R]
    (h : ∀ n : ℕ, IsCoherentRing (MvPolynomial (Fin n) R)) :
    IsUniversallyCoherent.{u, v} R where
  isCoherentRing A := by
    intros
    obtain ⟨n, I, e, hI⟩ := Algebra.FinitePresentation.iff.mp
      (inferInstance : Algebra.FinitePresentation R A)
    let _ : IsCoherentRing (MvPolynomial (Fin n) R) := h n
    let _ : Module.IsCoherent (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R ⧸ I) :=
      Module.IsCoherent.quotient I hI
    let _ : IsCoherentRing (MvPolynomial (Fin n) R ⧸ I) :=
      ⟨Module.IsCoherent.of_restrictScalars (MvPolynomial (Fin n) R)
        (S := MvPolynomial (Fin n) R ⧸ I) (N := MvPolynomial (Fin n) R ⧸ I)⟩
    exact isCoherentRing_of_ringEquiv e.toRingEquiv

/-- Universal coherence at the base-ring universe is equivalent to coherence of all
finite-variable polynomial rings over the base. -/
theorem iff_forall_mvPolynomial (R : Type u) [CommRing R] :
    IsUniversallyCoherent.{u, u} R ↔
      ∀ n : ℕ, IsCoherentRing (MvPolynomial (Fin n) R) := by
  constructor
  · intro hR n
    let _ : IsUniversallyCoherent.{u, u} R := hR
    exact IsUniversallyCoherent.isCoherentRing R (MvPolynomial (Fin n) R)
  · exact of_forall_mvPolynomial R

private theorem isCoherentRing_of_ulift.{liftExtra}
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    [IsUniversallyCoherent.{u, max v liftExtra} R] : IsCoherentRing A := by
  let e : A ≃ₐ[R] ULift.{liftExtra} A := (ULift.algEquiv (R := R)).symm
  let _ : Algebra.FinitePresentation R (ULift.{liftExtra} A) :=
    Algebra.FinitePresentation.equiv e
  let _ : IsCoherentRing (ULift.{liftExtra} A) :=
    IsUniversallyCoherent.isCoherentRing R (ULift.{liftExtra} A)
  exact isCoherentRing_of_ringEquiv e.symm.toRingEquiv

/-- Universal coherence in a target universe at least as large as the base-ring universe
implies universal coherence in any independently chosen target universe.
This theorem does not change the target algebra or its given algebra structure. -/
theorem changeTargetUniverse.{sourceExtra} (R : Type u) [CommRing R]
    [IsUniversallyCoherent.{u, max u sourceExtra} R] :
    IsUniversallyCoherent.{u, v} R := by
  apply of_forall_mvPolynomial R
  intro n
  exact isCoherentRing_of_ulift.{u, u, sourceExtra} R (MvPolynomial (Fin n) R)

/-- Polynomial rings in an arbitrary type of variables over a universally coherent
commutative ring are universally coherent in any target-algebra universe.

The source universal-coherence hypothesis is at the base-ring universe. The proof descends each
finite row to its finite variable support and uses the monomial basis in the remaining variables
to compare kernels by flat base change. -/
theorem mvPolynomial (R : Type u) [CommRing R]
    [IsUniversallyCoherent.{u, u} R] (σ : Type v) :
    IsUniversallyCoherent.{max u v, w} (MvPolynomial σ R) := by
  classical
  have h (τ : Type v) : IsCoherentRing (MvPolynomial τ R) := by
    let D := MvPolynomial τ R
    refine ⟨Module.IsCoherent.iff_finite_and_fg_ker.mpr ⟨inferInstance, ?_⟩⟩
    intro n g
    -- All entries of the row lie in one finite-variable polynomial subalgebra.
    let p : Fin n → D := fun i => g (Pi.single i 1)
    let F : Finset τ := Finset.univ.biUnion fun i => (p i).vars
    let s : Set τ := ↑F
    let ι : Type v := s
    let κ : Type v := ↥(sᶜ)
    let A := MvPolynomial ι R
    let Q := MvPolynomial κ A
    let j : A →ₐ[R] D := MvPolynomial.rename ((↑) : ι → τ)
    let a : Fin n → A := fun i =>
      (p i).killCompl (f := ((↑) : ι → τ)) Subtype.val_injective
    have ha (i : Fin n) : j (a i) = p i := by
      have hs : ((p i).vars : Set τ) ⊆ s := by
        intro x hx
        change x ∈ F
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
      obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
        (p i) ((↑) : ι → τ) Subtype.val_injective (by
          rw [Subtype.range_coe]
          exact hs)
      change MvPolynomial.rename ((↑) : ι → τ)
        ((p i).killCompl (f := ((↑) : ι → τ)) Subtype.val_injective) = p i
      rw [← hq, MvPolynomial.killCompl_rename_app]
    let _ : Finite ι := inferInstance
    let _ : IsUniversallyCoherent.{u, max u v} R := changeTargetUniverse R
    let _ : IsCoherentRing A := IsUniversallyCoherent.isCoherentRing R A
    let _ : Algebra A D := j.toRingHom.toAlgebra
    let _ : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq fun r => by
      change (MvPolynomial.C r : D) = j (MvPolynomial.C r)
      exact (MvPolynomial.rename_C _ r).symm
    let _ : IsScalarTower A D D := IsScalarTower.right
    -- The complementary monomials give a basis for this particular chart extension.
    let vF : κ ⊕ ι ≃ τ :=
      (Equiv.sumComm κ ι).trans (Equiv.Set.sumCompl s)
    let E : D ≃ₐ[R] Q :=
      (MvPolynomial.renameEquiv R vF.symm).trans (MvPolynomial.sumAlgEquiv R κ ι)
    have hE : E.toAlgHom.comp j = IsScalarTower.toAlgHom R A Q := by
      apply MvPolynomial.algHom_ext
      intro i
      have hi : vF.symm i.val = Sum.inr i := by
        apply vF.injective
        rw [vF.apply_symm_apply]
        exact (Equiv.Set.sumCompl_apply_inl s i).symm
      change (MvPolynomial.sumAlgEquiv R κ ι)
        (MvPolynomial.rename vF.symm
          (MvPolynomial.rename ((↑) : ι → τ) (MvPolynomial.X i))) =
        MvPolynomial.C (MvPolynomial.X i)
      rw [MvPolynomial.rename_X, MvPolynomial.rename_X, hi,
        MvPolynomial.sumAlgEquiv_X_inr]
    let EA : D ≃ₐ[A] Q :=
      { E.toRingEquiv with commutes' := fun a => AlgHom.congr_fun hE a }
    let b : Module.Basis (κ →₀ ℕ) A D :=
      (MvPolynomial.basisMonomials κ A).map EA.symm.toLinearEquiv
    let _ : Module.Free A D := Module.Free.of_basis b
    let _ : Module.Flat A D := Module.Flat.of_free
    let rA : (Fin n → A) →ₗ[A] A :=
      { toFun := fun x => ∑ i, x i * a i
        map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          change (∑ i, (c * x i) * a i) = c * ∑ i, x i * a i
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_assoc c (x i) (a i) }
    let rD : (Fin n → D) →ₗ[D] D :=
      { toFun := fun x => ∑ i, x i * p i
        map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          change (∑ i, (c * x i) * p i) = c * ∑ i, x i * p i
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_assoc c (x i) (p i) }
    have hrD : rD = g := by
      apply LinearMap.ext
      intro x
      change (∑ i, x i * p i) = g x
      calc
        (∑ i, x i * p i) = ∑ i, g (Pi.single i (x i)) := by
          apply Finset.sum_congr rfl
          intro i _
          have hs : Pi.single i (x i) = x i • Pi.single i (1 : D) := by
            simpa only [smul_eq_mul, mul_one] using (Pi.single_smul' i (x i) (1 : D))
          simpa only [p, map_smul, smul_eq_mul] using (congrArg g hs).symm
        _ = g (∑ i, Pi.single i (x i)) := by rw [map_sum]
        _ = g x := by rw [LinearMap.sum_single_apply]
    let h2 : (Fin n → A) →ₗ[A] (Fin n → D) :=
      { toFun := fun x i => j (x i)
        map_add' := fun x y => by funext i; exact j.map_add _ _
        map_smul' := fun c x => by
          funext i
          change j (c * x i) = c • j (x i)
          rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          exact j.map_mul _ _ }
    let h3 : A →ₗ[A] D := Algebra.linearMap A D
    have square (x : Fin n → A) : rD (h2 x) = j (rA x) := by
      change (∑ i, j (x i) * p i) = j (∑ i, x i * a i)
      simp only [map_sum, map_mul, ha]
    let KA : Submodule A (Fin n → A) := LinearMap.ker rA
    let KD : Submodule D (Fin n → D) := LinearMap.ker rD
    let h1 : KA →ₗ[A] KD :=
      (h2.comp KA.subtype).codRestrict (KD.restrictScalars A) fun x => by
        change rD (h2 x.val) = 0
        rw [square, show rA x.val = 0 from x.property, map_zero]
    -- Flat base change identifies the kernels without any surjectivity assumption on the row.
    have H2 : IsBaseChange D h2 :=
      IsBaseChange.of_equiv (TensorProduct.piScalarRight A D D (Fin n))
        (fun x => by
          funext i
          rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
          change x i • (1 : D) = j (x i)
          rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
          exact congrFun (AlgHom.coe_toRingHom j) (x i))
    have H3 : IsBaseChange D h3 := IsBaseChange.linearMap A D
    have H1 : IsBaseChange D h1 :=
      IsBaseChange.of_left_exact D h1 h2 h3
        (f := KA.subtype) (g := rA) (f' := KD.subtype) (g' := rD)
        (by ext x i; rfl)
        (LinearMap.ext fun x => (square x).symm)
        H2 H3
        (LinearMap.exact_subtype_ker_map rA) (Submodule.injective_subtype KA)
        (LinearMap.exact_subtype_ker_map rD) (Submodule.injective_subtype KD)
    have hKA : KA.FG :=
      (Module.IsCoherent.iff_finite_and_fg_ker.mp
        (inferInstance : Module.IsCoherent A A)).2 n rA
    let _ : Module.Finite A KA := Module.Finite.of_fg hKA
    let _ : Module.Finite D (TensorProduct A D KA) := Module.Finite.base_change A D KA
    let _ : Module.Finite D KD := Module.Finite.equiv H1.equiv
    have hKD : KD.FG := Module.Finite.iff_fg.mp inferInstance
    simpa only [KD, hrD] using hKD
  refine of_forall_mvPolynomial (MvPolynomial σ R) fun n => ?_
  let _ : IsCoherentRing (MvPolynomial (Fin n ⊕ σ) R) := h (Fin n ⊕ σ)
  exact isCoherentRing_of_ringEquiv (MvPolynomial.sumAlgEquiv R (Fin n) σ).toRingEquiv

/-- Arbitrary localizations of a universally coherent commutative ring are universally
coherent in any independently chosen target-algebra universe.

The source universal-coherence hypothesis is at the base-ring universe. The proof uses
coherence of localized modules and the finite-polynomial criterion; neither finitely many
denominators nor algebra finite presentation of the localization is required. -/
theorem of_isLocalization
    {R : Type u} [CommRing R] [IsUniversallyCoherent.{u, u} R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization M S] : IsUniversallyCoherent.{v, w} S := by
  refine of_forall_mvPolynomial S fun n => ?_
  let _ : IsCoherentRing (MvPolynomial (Fin n) R) :=
    IsUniversallyCoherent.isCoherentRing R (MvPolynomial (Fin n) R)
  let _ : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
    MvPolynomial.algebraMvPolynomial
  exact ⟨Module.IsCoherent.of_isLocalizedModule (M.map (MvPolynomial.C (σ := Fin n)))
    (Algebra.linearMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S))⟩

end IsUniversallyCoherent
