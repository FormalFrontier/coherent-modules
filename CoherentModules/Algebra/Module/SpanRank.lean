/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.SpanRank

/-!
# Generators of semilinear images

Taking the span over the target semiring allows generator bounds for a semilinear map
without assuming that its scalar homomorphism is surjective. The cardinal bound applies to
arbitrary submodules. The natural-valued bound assumes finite generation of the source.
-/

@[expose] public section

universe uR uS uM uN

namespace Submodule

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module S N] {σ : R →+* S}

/-- Spanning before taking a semilinear image does not change its target-scalar span. -/
lemma span_image_span (f : M →ₛₗ[σ] N) (s : Set M) :
    span S (f '' (span R s : Set M)) = span S (f '' s) := by
  apply le_antisymm
  · exact span_le.mpr (image_span_subset_span f s)
  · apply span_mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, subset_span hx, rfl⟩

/-- The target-scalar span of a semilinear image needs no more generators than its source.
The lifts compare generator cardinals in independent module universes. -/
lemma lift_spanRank_span_image_le (f : M →ₛₗ[σ] N) (p : Submodule R M) :
    Cardinal.lift.{uM} (span S (f '' (p : Set M))).spanRank ≤
      Cardinal.lift.{uN} p.spanRank := by
  obtain ⟨s, hcard, hspan⟩ := p.exists_span_set_card_eq_spanRank
  have himage : span S (f '' (p : Set M)) = span S (f '' s) := by
    rw [← hspan, span_image_span]
  rw [himage]
  calc
    Cardinal.lift.{uM} (span S (f '' s)).spanRank ≤
        Cardinal.lift.{uM} (Cardinal.mk (f '' s)) :=
      Cardinal.lift_le.mpr (spanRank_span_le_card (f '' s))
    _ ≤ Cardinal.lift.{uN} (Cardinal.mk s) := Cardinal.mk_image_le_lift
    _ = Cardinal.lift.{uN} p.spanRank := congrArg Cardinal.lift hcard

/-- The target-scalar span of the image of a finitely generated submodule is finitely generated. -/
lemma FG.span_image {p : Submodule R M} (hp : p.FG) (f : M →ₛₗ[σ] N) :
    (span S (f '' (p : Set M))).FG := by
  classical
  obtain ⟨s, _, hs⟩ := hp.exists_span_finset_card_eq_spanFinrank
  refine ⟨s.image f, ?_⟩
  rw [Finset.coe_image, ← span_image_span, hs]

/-- For a finitely generated source, a semilinear image has no larger minimum finite number
of generators. Finite generation is necessary because `spanFinrank` is zero for an
infinitely generated submodule. -/
lemma spanFinrank_span_image_le_of_fg (f : M →ₛₗ[σ] N) {p : Submodule R M} (hp : p.FG) :
    (span S (f '' (p : Set M))).spanFinrank ≤ p.spanFinrank := by
  have h := lift_spanRank_span_image_le f p
  rw [(hp.span_image f).spanRank_eq_spanFinrank, hp.spanRank_eq_spanFinrank] at h
  simpa using h

end Submodule
