/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.Module.SpanRank

universe uR uS uM uN

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module S N] {σ : R →+* S}

-- Surjectivity of the scalar homomorphism is needed only for the raw-map specialization.
example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : Submodule R M) :
    Cardinal.lift.{uM} (p.map f).spanRank ≤ Cardinal.lift.{uN} p.spanRank := by
  simpa only [Submodule.span_image, Submodule.span_eq] using
    Submodule.lift_spanRank_span_image_le f p

-- A surjective semilinear map sends any spanning set to target-scalar generators,
-- even when its scalar homomorphism is not surjective.
example (f : M →ₛₗ[σ] N) (hf : Function.Surjective f) {s : Set M}
    (hs : Submodule.span R s = ⊤) : Submodule.span S (f '' s) = ⊤ := by
  rw [← Submodule.span_image_span f s, hs]
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  exact Submodule.subset_span ⟨x, by trivial, rfl⟩
