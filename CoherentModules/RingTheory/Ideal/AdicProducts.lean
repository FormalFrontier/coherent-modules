/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicLocality
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Prod

/-!
# Submodule adic cofinality in finite products

An arbitrary ideal of a finite product of commutative rings has submodule adic
cofinality if and only if its image under every coordinate projection does.
The same criterion holds for finite-submodule adic cofinality. The `Ideal.pi`
and `Ideal.prod` criteria specialize these results to the usual product ideals.
Empty products and zero-ring factors are included.

Full submodule adic cofinality allows every submodule of a finite ambient module;
the finite-submodule variant asks only that the submodule be finitely generated.
Neither criterion requires the ideal to be finitely generated or the ambient
module to be finitely presented. The existing `.cofinal` eliminators retain the
given scalar action and allow an independent module universe.

## Implementation notes

Coordinate idempotents span the unit ideal for a finite product. Each coordinate
ring, with its projection algebra, is the localization away from the corresponding
idempotent. Uniqueness of localization and finite-algebra ascent transport the
coordinate properties to the quotient localization models used by the near-`V(I)`
criterion in `CoherentModules.RingTheory.Ideal.AdicLocality`.
The binary proof uses the two complementary idempotents directly, so the two
rings may lie in independent universes. Finiteness of the index is essential for
the reverse implication; projection ascent itself does not need it.

## References

The predicates are Fujiwara--Kato's conditions (AP) and (APf), as documented in
`CoherentModules.RingTheory.Ideal.AdicCompatibility`. The proofs reuse the
near-`V(I)` locality formalization in
`CoherentModules.RingTheory.Ideal.AdicLocality`.

The Mathlib ingredients come from the ideal modules by Kenny Lau, Chris Hughes,
Mario Carneiro and Markus Himmel; the localization modules by Kenny Lau,
Mario Carneiro, Johan Commelin, Amelia Livingston and Anne Baanen; Johan Commelin's
module-finiteness API; and the Pi-ring module by Simon Hudon and Patrick Massot.
-/

@[expose] public section

universe uι uR uS

namespace Ideal

private theorem isLocalization_away_evalRingHom
    {ι : Type uι} [DecidableEq ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] (i : ι) :
    @IsLocalization.Away (Π j, R j) _ (Pi.single i (1 : R i)) (R i) _
      (Pi.evalRingHom R i).toAlgebra := by
  let := (Pi.evalRingHom R i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom R i)
    (Pi.evalRingHom R i).surjective
  simp [IsIdempotentElem, ← Pi.single_mul_left]

-- Transport a coordinate property to the quotient Away model without changing
-- the algebra structures used in the public statements.
private theorem hasSubmoduleAdicCofinality_map_away_of_isLocalization
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : R) [IsLocalization.Away f S]
    (hI : (I.map (algebraMap R S)).HasSubmoduleAdicCofinality) :
    (I.map (algebraMap R (Localization.Away f))).HasSubmoduleAdicCofinality := by
  let e : Localization.Away f ≃ₐ[R] S := Localization.algEquiv (Submonoid.powers f) S
  have he : e.symm.toRingEquiv.toRingHom.comp (algebraMap R S) =
      algebraMap R (Localization.Away f) := e.symm.toAlgHom.comp_algebraMap
  let : Algebra S (Localization.Away f) := e.symm.toRingEquiv.toRingHom.toAlgebra
  let : Module.Finite S (Localization.Away f) := e.symm.toRingEquiv.finite
  simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_map, he] using
    (hI.map (S := Localization.Away f))

private theorem hasFiniteSubmoduleAdicCofinality_map_away_of_isLocalization
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : R) [IsLocalization.Away f S]
    (hI : (I.map (algebraMap R S)).HasFiniteSubmoduleAdicCofinality) :
    (I.map (algebraMap R (Localization.Away f))).HasFiniteSubmoduleAdicCofinality := by
  let e : Localization.Away f ≃ₐ[R] S := Localization.algEquiv (Submonoid.powers f) S
  have he : e.symm.toRingEquiv.toRingHom.comp (algebraMap R S) =
      algebraMap R (Localization.Away f) := e.symm.toAlgHom.comp_algebraMap
  let : Algebra S (Localization.Away f) := e.symm.toRingEquiv.toRingHom.toAlgebra
  let : Module.Finite S (Localization.Away f) := e.symm.toRingEquiv.finite
  simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_map, he] using
    (hI.map (S := Localization.Away f))

private theorem span_prod_idempotents
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S] :
    Ideal.span ({(1, 0), (0, 1)} : Set (R × S)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).2
  refine Ideal.mem_span_pair.mpr ⟨1, 1, ?_⟩
  ext <;> simp

/-- An arbitrary ideal of a finite product has submodule adic cofinality exactly
when all its coordinate images do. Empty products and zero factors are allowed;
no finite generation of the ideal or of the test submodules is required. -/
theorem hasSubmoduleAdicCofinality_iff_forall_map_evalRingHom
    {ι : Type uι} [Finite ι]
    {R : ι → Type uR} [∀ i, CommRing (R i)]
    (I : Ideal (Π i, R i)) :
    I.HasSubmoduleAdicCofinality ↔
      ∀ i, (I.map (Pi.evalRingHom R i)).HasSubmoduleAdicCofinality := by
  classical
  constructor
  · intro hI i
    let : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
    let : Module.Finite (Π j, R j) (R i) :=
      RingHom.Finite.of_surjective _ (Pi.evalRingHom R i).surjective
    simpa only [RingHom.algebraMap_toAlgebra] using (hI.map (S := R i))
  · intro h
    have hcover : I ⊔ Ideal.span (Set.range fun i ↦ (Pi.single i 1 : Π j, R j)) = ⊤ := by
      rw [Ideal.span_single_eq_top R, sup_top_eq]
    apply (hasSubmoduleAdicCofinality_iff_forall_map_away I _ hcover).2
    rintro _ ⟨i, rfl⟩
    let : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
    let : IsLocalization.Away (Pi.single i (1 : R i)) (R i) :=
      isLocalization_away_evalRingHom R i
    apply hasSubmoduleAdicCofinality_map_away_of_isLocalization (S := R i)
    simpa only [RingHom.algebraMap_toAlgebra] using h i

/-- An arbitrary ideal of a finite product has finite-submodule adic cofinality
exactly when all its coordinate images do. Only the test submodule is required
to be finitely generated, and empty products and zero factors are allowed. -/
theorem hasFiniteSubmoduleAdicCofinality_iff_forall_map_evalRingHom
    {ι : Type uι} [Finite ι]
    {R : ι → Type uR} [∀ i, CommRing (R i)]
    (I : Ideal (Π i, R i)) :
    I.HasFiniteSubmoduleAdicCofinality ↔
      ∀ i, (I.map (Pi.evalRingHom R i)).HasFiniteSubmoduleAdicCofinality := by
  classical
  constructor
  · intro hI i
    let : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
    let : Module.Finite (Π j, R j) (R i) :=
      RingHom.Finite.of_surjective _ (Pi.evalRingHom R i).surjective
    simpa only [RingHom.algebraMap_toAlgebra] using (hI.map (S := R i))
  · intro h
    have hcover : I ⊔ Ideal.span (Set.range fun i ↦ (Pi.single i 1 : Π j, R j)) = ⊤ := by
      rw [Ideal.span_single_eq_top R, sup_top_eq]
    apply (hasFiniteSubmoduleAdicCofinality_iff_forall_map_away I _ hcover).2
    rintro _ ⟨i, rfl⟩
    let : Algebra (Π j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
    let : IsLocalization.Away (Pi.single i (1 : R i)) (R i) :=
      isLocalization_away_evalRingHom R i
    apply hasFiniteSubmoduleAdicCofinality_map_away_of_isLocalization (S := R i)
    simpa only [RingHom.algebraMap_toAlgebra] using h i

/-- A finite family product ideal has submodule adic cofinality exactly when
each ideal in the family does. -/
theorem hasSubmoduleAdicCofinality_pi_iff
    {ι : Type uι} [Finite ι]
    {R : ι → Type uR} [∀ i, CommRing (R i)]
    (I : Π i, Ideal (R i)) :
    (Ideal.pi I).HasSubmoduleAdicCofinality ↔
      ∀ i, (I i).HasSubmoduleAdicCofinality := by
  simpa only [Ideal.map_evalRingHom_pi] using
    (hasSubmoduleAdicCofinality_iff_forall_map_evalRingHom (Ideal.pi I))

/-- A finite family product ideal has finite-submodule adic cofinality exactly
when each ideal in the family does. -/
theorem hasFiniteSubmoduleAdicCofinality_pi_iff
    {ι : Type uι} [Finite ι]
    {R : ι → Type uR} [∀ i, CommRing (R i)]
    (I : Π i, Ideal (R i)) :
    (Ideal.pi I).HasFiniteSubmoduleAdicCofinality ↔
      ∀ i, (I i).HasFiniteSubmoduleAdicCofinality := by
  simpa only [Ideal.map_evalRingHom_pi] using
    (hasFiniteSubmoduleAdicCofinality_iff_forall_map_evalRingHom (Ideal.pi I))

/-- A binary product ideal has submodule adic cofinality exactly when both
factor ideals do. The rings may lie in independent universes. -/
theorem hasSubmoduleAdicCofinality_prod_iff
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) :
    (I.prod J).HasSubmoduleAdicCofinality ↔
      I.HasSubmoduleAdicCofinality ∧ J.HasSubmoduleAdicCofinality := by
  constructor
  · intro h
    constructor
    · let : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
      let : Module.Finite (R × S) R :=
        RingHom.Finite.of_surjective _ (RingHom.fst R S).surjective
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_fst_prod] using (h.map (S := R))
    · let : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
      let : Module.Finite (R × S) S :=
        RingHom.Finite.of_surjective _ (RingHom.snd R S).surjective
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_snd_prod] using (h.map (S := S))
  · rintro ⟨hI, hJ⟩
    have hcover : I.prod J ⊔ Ideal.span ({(1, 0), (0, 1)} : Set (R × S)) = ⊤ := by
      rw [span_prod_idempotents, sup_top_eq]
    apply (hasSubmoduleAdicCofinality_iff_forall_map_away (I.prod J) _ hcover).2
    rintro f (rfl | rfl)
    · let : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
      let : IsLocalization.Away (R := R × S) (1, 0) R := IsLocalization.away_fst
      apply hasSubmoduleAdicCofinality_map_away_of_isLocalization (S := R)
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_fst_prod] using hI
    · let : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
      let : IsLocalization.Away (R := R × S) (0, 1) S := IsLocalization.away_snd
      apply hasSubmoduleAdicCofinality_map_away_of_isLocalization (S := S)
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_snd_prod] using hJ

/-- A binary product ideal has finite-submodule adic cofinality exactly when
both factor ideals do. The rings may lie in independent universes. -/
theorem hasFiniteSubmoduleAdicCofinality_prod_iff
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) :
    (I.prod J).HasFiniteSubmoduleAdicCofinality ↔
      I.HasFiniteSubmoduleAdicCofinality ∧
        J.HasFiniteSubmoduleAdicCofinality := by
  constructor
  · intro h
    constructor
    · let : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
      let : Module.Finite (R × S) R :=
        RingHom.Finite.of_surjective _ (RingHom.fst R S).surjective
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_fst_prod] using (h.map (S := R))
    · let : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
      let : Module.Finite (R × S) S :=
        RingHom.Finite.of_surjective _ (RingHom.snd R S).surjective
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_snd_prod] using (h.map (S := S))
  · rintro ⟨hI, hJ⟩
    have hcover : I.prod J ⊔ Ideal.span ({(1, 0), (0, 1)} : Set (R × S)) = ⊤ := by
      rw [span_prod_idempotents, sup_top_eq]
    apply (hasFiniteSubmoduleAdicCofinality_iff_forall_map_away (I.prod J) _ hcover).2
    rintro f (rfl | rfl)
    · let : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
      let : IsLocalization.Away (R := R × S) (1, 0) R := IsLocalization.away_fst
      apply hasFiniteSubmoduleAdicCofinality_map_away_of_isLocalization (S := R)
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_fst_prod] using hI
    · let : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
      let : IsLocalization.Away (R := R × S) (0, 1) S := IsLocalization.away_snd
      apply hasFiniteSubmoduleAdicCofinality_map_away_of_isLocalization (S := S)
      simpa only [RingHom.algebraMap_toAlgebra, Ideal.map_snd_prod] using hJ

end Ideal
