/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Coherent
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Finite-support trivial square-zero extensions

For a division ring `D`, the trivial square-zero extension by `ι →₀ D` is left coherent
exactly when `ι` is finite. The left action is the usual pointwise action, while the
right module structure can be any given one commuting with it. The universes of `D`
and `ι` are independent, and the index type may be empty.

Over a field, the canonical inclusion algebra on this extension is faithfully flat.
An infinite index type therefore gives a faithfully flat algebra which is not coherent.
Its scalar action is coordinatewise, and its algebra map is `a ↦ (a, 0)`, as expressed
by `TrivSqZeroExt.algebraMap_eq_inl`.

## References

The proofs combine the bimodule coherence criterion in
`CoherentModules.Algebra.TrivSqZeroExt.Coherent` with Mathlib's standard Finsupp basis,
finite-generation API, and faithful flatness of nontrivial free modules.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

section DivisionRing

variable {D : Type u} [DivisionRing D] {ι : Type v}
  [rightModule : Module Dᵐᵒᵖ (ι →₀ D)]
  [commutation :
    @SMulCommClass D Dᵐᵒᵖ (ι →₀ D)
      (Finsupp.smulZeroClass (α := ι) (R := D) (M := D)).toSMul
      rightModule.toDistribMulAction.toDistribSMul.toSMulZeroClass.toSMul]

/-- A finite-support idealization of a division ring is left coherent exactly when its
index type is finite. The left module is the usual Finsupp module, and the ring uses
the given compatible right module without any centrality assumption. The index type
may be empty. -/
theorem isCoherentRing_finsupp_iff_finite :
    @IsCoherentRing (TrivSqZeroExt D (ι →₀ D))
      (@TrivSqZeroExt.ring D (ι →₀ D)
        (inferInstance : Ring D)
        (inferInstance : AddCommGroup (ι →₀ D))
        (Finsupp.module (R := D) ι D)
        rightModule commutation) ↔ Finite ι := by
  rw [isCoherentRing_iff_finite_of_divisionRing D (ι →₀ D)]
  constructor
  · intro h
    let _ : Module.Finite D (ι →₀ D) := h
    exact Module.Finite.finite_basis (Finsupp.basisSingleOne (ι := ι) (R := D))
  · intro h
    let _ : Finite ι := h
    infer_instance

/-- An infinite index obstructs left coherence of a finite-support idealization,
for every compatible right module structure on the coefficient module. -/
theorem not_isCoherentRing_finsupp [Infinite ι] :
    ¬ IsCoherentRing (TrivSqZeroExt D (ι →₀ D)) := by
  intro h
  exact ((isCoherentRing_finsupp_iff_finite (D := D) (ι := ι)).mp h).not_infinite
    inferInstance

end DivisionRing

open scoped TrivSqZeroExt in
/-- The canonical idealization of a finite-support vector space over a field is faithfully
flat but not coherent when the index type is infinite. Its algebra map is `a ↦ (a, 0)`
and its scalar action is coordinatewise. Faithful flatness uses the nontrivial field
coordinate and freeness over the field, not faithful flatness of the coefficient module. -/
theorem finsupp_faithfullyFlat_and_not_isCoherentRing
    {k : Type u} [Field k] {ι : Type v} [Infinite ι] :
    Module.FaithfullyFlat k (TrivSqZeroExt k (ι →₀ k)) ∧
      ¬ IsCoherentRing (TrivSqZeroExt k (ι →₀ k)) := by
  constructor
  · exact @Module.FaithfullyFlat.instOfNontrivialOfFree k (TrivSqZeroExt k (ι →₀ k))
      inferInstance inferInstance inferInstance
      TrivSqZeroExt.instNontrivial_of_left
      (Module.Free.of_divisionRing k (TrivSqZeroExt k (ι →₀ k)))
  · exact not_isCoherentRing_finsupp

end TrivSqZeroExt
