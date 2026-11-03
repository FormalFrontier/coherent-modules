/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor
-/
module

public import CoherentModules.Basic
public import CoherentModules.Localization
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Polynomial.Basic

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
* `IsUniversallyCoherent.changeTargetUniverse`: base-universe universal coherence implies
  universal coherence in an arbitrary target universe.
* `IsUniversallyCoherent.of_isLocalization`: arbitrary localizations of base-universe
  universally coherent rings are universally coherent in any target universe.

The finite-polynomial criterion reuses Mathlib's algebra finite-presentation quotient
characterization, together with coherent-module quotients and scalar-restriction transport.
Localization closure reuses coherent-module localization and Mathlib's polynomial-localization
instance.
-/

@[expose] public section

universe u v w

/-- A commutative ring is universally coherent (for target algebras in `Type v`) if every
finitely presented commutative algebra in that universe is a coherent ring.

The target-algebra universe is deliberately independent of the universe containing the base
ring. Use `IsUniversallyCoherent.{u, v} R` when that universe is not inferred from an algebra. -/
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
    [IsCoherentRing A] (e : A ≃+* B) : IsCoherentRing B := by
  let _ : Module A B := Module.compHom B e.toRingHom
  let eAB : A ≃ₗ[A] B := Module.compHom.toLinearEquiv e
  let _ : Module.IsCoherent A B := Module.IsCoherent.of_equiv eAB
  let _ : IsScalarTower A B B := SMul.comp.isScalarTower (e : A → B)
  exact ⟨Module.IsCoherent.of_restrictScalars A (S := B) (N := B)⟩

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

/-- Universal coherence at the base-ring universe implies universal coherence at any
independently chosen target universe. This theorem does not change the target algebra. -/
theorem changeTargetUniverse (R : Type u) [CommRing R] [IsUniversallyCoherent.{u, u} R] :
    IsUniversallyCoherent.{u, v} R :=
  of_forall_mvPolynomial R ((iff_forall_mvPolynomial R).mp inferInstance)

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
