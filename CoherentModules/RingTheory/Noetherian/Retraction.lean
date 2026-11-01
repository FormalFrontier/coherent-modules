/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Left Noetherianity and additive right retractions

Let `f : A →+* B` have an additive retraction `E : B →+ A` satisfying
`E (b * f a) = E b * a`. Extension followed by contraction fixes every left
ideal of `A`. Thus extension reflects the order of left ideals and transports
the ascending chain condition from `B` to `A`.

The retraction need not preserve multiplication. Its compatibility is with
multiplication on the right, whereas the ideals and Noetherianity are on the
left. No commutativity or additive inverses are needed.

## Implementation notes

The proof uses Mathlib's ideal spans and order-theoretic characterization of
Noetherian modules. The RingHom specialization recovers the contraction equality
from the inclusion in `Ideal.map_le_comap_of_inverse`.
-/

@[expose] public section

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [Semiring A] [Semiring B]

/-- Extension followed by contraction fixes a left ideal in the presence of an
additive retraction compatible with right multiplication by the image. -/
theorem comap_map_eq_of_additive_retraction
    (f : A →+* B) (E : B →+ A)
    (hE : ∀ a, E (f a) = a)
    (hmul : ∀ b a, E (b * f a) = E b * a) (J : Ideal A) :
    Ideal.comap f (Ideal.map f J) = J := by
  have hspan {x : B} (hx : x ∈ Ideal.map f J) : ∀ b, E (b * x) ∈ J := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro b
      rw [hmul]
      exact J.mul_mem_left _ ha
    | zero => intro b; simp
    | add x y _ _ hx hy =>
      intro b
      rw [mul_add, map_add]
      exact J.add_mem (hx b) (hy b)
    | smul b x _ hx =>
      intro c
      simpa only [smul_eq_mul, ← mul_assoc] using hx (c * b)
  apply le_antisymm
  · intro a ha
    simpa only [one_mul, hE] using hspan ha 1
  · exact Ideal.map_le_iff_le_comap.mp le_rfl

/-- For a ring-homomorphism retraction, the additive criterion specializes to
the contraction equality also obtained from `Ideal.map_le_comap_of_inverse`.
In particular, the additive criterion agrees with the ring-homomorphism case. -/
theorem comap_map_eq_of_leftInverse
    (f : A →+* B) (g : B →+* A) (h : Function.LeftInverse g f) (J : Ideal A) :
    Ideal.comap f (Ideal.map f J) = J :=
  f.comap_map_eq_of_additive_retraction g.toAddMonoidHom h
    (fun b a => by
      change g (b * f a) = g b * a
      rw [map_mul, h]) J

/-- Extension of left ideals reflects inclusion in the presence of an additive
retraction compatible with right multiplication by the image. -/
theorem ideal_map_le_iff_of_additive_retraction
    (f : A →+* B) (E : B →+ A)
    (hE : ∀ a, E (f a) = a)
    (hmul : ∀ b a, E (b * f a) = E b * a) (I J : Ideal A) :
    Ideal.map f I ≤ Ideal.map f J ↔ I ≤ J := by
  constructor
  · intro h
    simpa only [f.comap_map_eq_of_additive_retraction E hE hmul] using
      (Ideal.comap_mono (f := f) h)
  · exact Ideal.map_mono

/-- Left Noetherianity descends along a semiring homomorphism with an additive
right retraction. This concerns the regular left modules, not restriction of
scalars on the whole target semiring. -/
theorem isNoetherianRing_of_additive_retraction
    (f : A →+* B) (E : B →+ A)
    (hE : ∀ a, E (f a) = a)
    (hmul : ∀ b a, E (b * f a) = E b * a)
    [IsNoetherianRing B] : IsNoetherianRing A := by
  let e : Ideal A ↪o Ideal B := OrderEmbedding.ofMapLEIff (Ideal.map f)
    (f.ideal_map_le_iff_of_additive_retraction E hE hmul)
  exact isNoetherian_mk e.wellFoundedGT

end RingHom
