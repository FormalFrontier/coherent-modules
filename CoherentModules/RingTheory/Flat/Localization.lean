/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.DirectSum
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Faithful flatness of families of principal localizations

The dependent direct sum of the canonical localizations away from a family
of elements is faithfully flat if and only if the family spans the unit
ideal. Each localization is flat. When the generators span the unit ideal,
every proper ideal has a nontrivial quotient-tensor fiber in at least one
localization. The detecting localization may depend on the ideal; no individual
localization need be faithfully flat.

The ring and index type have independent universes. Arbitrary index types,
including the empty type, and subsingleton commutative rings are allowed.

## References

The proof specializes CoherentModules' joint proper-ideal criterion
`Module.FaithfullyFlat.directSum_iff`. It uses Mathlib's localization flatness,
disjoint-powers covering theorem `Ideal.exists_disjoint_powers_of_span_eq_top`,
localization-ideal criterion `IsLocalization.map_algebraMap_ne_top_iff_disjoint`,
and quotient-tensor equivalence `Ideal.qoutMapEquivTensorQout`.
-/

@[expose] public section

open scoped DirectSum TensorProduct

universe u v

namespace Module.FaithfullyFlat

private theorem nontrivial_quot_tensor_away_iff
    {R : Type u} [CommRing R] (I : Ideal R) (r : R) :
    Nontrivial ((R ⧸ I) ⊗[R] Localization.Away r) ↔
      Disjoint (Submonoid.powers r : Set R) (I : Set R) := by
  exact (TensorProduct.comm R (R ⧸ I) (Localization.Away r)).toEquiv.nontrivial_congr.trans <|
    (Ideal.qoutMapEquivTensorQout (R := R) (I := I)
      (Localization.Away r)).toEquiv.nontrivial_congr.symm.trans <|
    Ideal.Quotient.nontrivial_iff.trans <|
    IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (Submonoid.powers r) (Localization.Away r) I

/-- The dependent direct sum of the canonical principal localizations is
faithfully flat if and only if the generators span the unit ideal. Individual
localizations need not be faithfully flat: the detecting component in
`Module.FaithfullyFlat.directSum_iff` may depend on the proper ideal. The proof
uses Mathlib's disjoint-powers covering and localization-ideal criteria. -/
theorem directSum_away_iff (R : Type u) [CommRing R] {ι : Type v} (s : ι → R) :
    Module.FaithfullyFlat R (⨁ i, Localization.Away (s i)) ↔
      Ideal.span (Set.range s) = ⊤ := by
  classical
  rw [Module.FaithfullyFlat.directSum_iff R (fun i ↦ Localization.Away (s i))]
  constructor
  · rintro ⟨_, h⟩
    by_contra hspan
    obtain ⟨i, hi⟩ := h (Ideal.span (Set.range s)) hspan
    exact Set.disjoint_left.mp
      ((nontrivial_quot_tensor_away_iff _ (s i)).mp hi)
      (Submonoid.mem_powers (s i))
      (Ideal.mem_span_range_self (f := s) (x := i))
  · intro hspan
    refine ⟨fun i ↦ IsLocalization.flat (Localization.Away (s i)) (Submonoid.powers (s i)), ?_⟩
    intro I hI
    obtain ⟨r, ⟨i, rfl⟩, hdisjoint⟩ :=
      Ideal.exists_disjoint_powers_of_span_eq_top (Set.range s) hspan I hI
    exact ⟨i, (nontrivial_quot_tensor_away_iff I (s i)).mpr hdisjoint.symm⟩

end Module.FaithfullyFlat
