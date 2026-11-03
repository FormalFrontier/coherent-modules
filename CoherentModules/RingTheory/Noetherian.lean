/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.LinearMap.Evaluation

public import CoherentModules.RingTheory.Ideal.Annihilator
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Noetherianity for scalar clearing, annihilator quotients, and Hom modules

For a semilinear map, suppose each target element can be multiplied by a scalar
with a left inverse into the image. Comap then reflects submodule order, so the
ascending-chain criterion transfers Noetherianity from source to target. In
particular, clearing by target units suffices. Neither the scalar homomorphism
nor the semilinear map needs to be surjective.

For regular semiring modules, unit clearing also identifies each left ideal
with the extension of its contraction. Units need not be central or come from
the source. Function-surjective maps satisfy unit clearing with the unit `1`.

Suppose a ring `A` and a semiring `C` act on the same additive commutative monoid
`M`, and the given actions commute. Finite generation over `C` and Noetherianity
over `A` imply that `A` modulo the annihilator of its given action is left
Noetherian. The scalar types and module carrier have independent universes, and
neither scalar type needs to be Noetherian. The proof uses the `A`-module of
`C`-linear endomorphisms, not Noetherianity of their ring.

Taking `C = A` gives necessity in the annihilator-quotient criterion for an
additive commutative group whose given scalar action commutes with itself.
Conversely, for an additive commutative monoid over a ring, finite generation
over that ring and left Noetherianity of its annihilator quotient imply
Noetherianity, without commuting scalar actions. Self-commutation means
`a • (b • m) = b • (a • m)` for the original action, not commutativity of the ring.

For a Noetherian module over a commutative ring, containment of ideal radicals
after adding its annihilator gives a uniform ideal-power bound on the original
module. No Noetherianity of the scalar ring or finite generation of the original
ideals is required.

Semilinear maps from a finitely generated semimodule to a Noetherian module over
a ring form a Noetherian module for the canonical pointwise action, provided
the two codomain actions commute. The scalar homomorphism is arbitrary, and
no action on the source by the external ring is needed. The ring hypothesis
on the external scalars is essential: Noetherian semimodules over a semiring
need not be closed under finite products.

## References

The argument uses Mathlib's submodule comap and ascending-chain criterion, and
extends the ideal unit-clearing argument in this library to semimodules. The
left-inverse formulation retains only the scalar recovery needed in that argument.
The commutative annihilator-quotient criterion follows the formalization in
Adic Modules by Formal Frontier Agents. The two-scalar generalization uses this
library's commuting-action Hom theorem and Mathlib's canonical pointwise
linear-map actions. The scalar representation formed with
`LinearMap.toSpanSingleton` at the identity endomorphism sends `a` to `m ↦ a • m`.
Its range is a Noetherian `A`-module and its kernel is the original annihilator.
Mathlib's first isomorphism theorem and quotient-ring scalar tower then give
left Noetherianity of the quotient.
The semilinear Hom theorem generalizes Mathlib's `isNoetherian_linearMap` by
embedding Hom into a finite product of the codomain via generator evaluation.
It uses Mathlib's semilinear extensionality and injective Noetherianity transfer.
-/

@[expose] public section

universe uR uR₂ uS uM uN

section Semiring

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

section Module

variable {M : Type uM} {N : Type uN} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module S N] {φ : R →+* S}

/-- Comap reflects submodule order if every target element can be cleared into
the image by a scalar with a left inverse. The inverse is on the left because
these are left semimodules. -/
theorem Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range (f : M →ₛₗ[φ] N)
    (hclear : ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n)
    {p q : Submodule S N} : p.comap f ≤ q.comap f ↔ p ≤ q := by
  constructor
  · intro h n hn
    obtain ⟨m, a, b, hba, hm⟩ := hclear n
    have hmp : m ∈ p.comap f := by
      rw [Submodule.mem_comap, hm]
      exact p.smul_mem a hn
    have hmq : f m ∈ q := Submodule.mem_comap.mp (h hmp)
    have hrecover : b • f m = n := by
      rw [hm, ← mul_smul, hba, one_smul]
    rw [← hrecover]
    exact q.smul_mem b hmq
  · exact Submodule.comap_mono

/-- Noetherianity ascends along a semilinear map if every target element can be
cleared into its image by a scalar with a left inverse. No surjectivity of the
scalar homomorphism is required. -/
theorem isNoetherian_of_left_inv_smul_mem_range (f : M →ₛₗ[φ] N)
    [IsNoetherian R M]
    (hclear : ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n) :
    IsNoetherian S N := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro c
  let d : ℕ →o Submodule R M :=
    ⟨fun i => (c i).comap f, fun _ _ hij => Submodule.comap_mono (c.monotone hij)⟩
  obtain ⟨i, hi⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R M)) d
  refine ⟨i, fun j hij => ?_⟩
  apply le_antisymm
  · exact (Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range f hclear).mp
      (le_of_eq (hi j hij))
  · exact (Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range f hclear).mp
      (le_of_eq (hi j hij).symm)

/-- Noetherianity ascends along a semilinear map when each target element can be
cleared into the image by a target unit. The units may depend on the element
and need not come from the source. -/
theorem isNoetherian_of_unit_smul_mem_range (f : M →ₛₗ[φ] N) [IsNoetherian R M]
    (hunit : ∀ n : N, ∃ m : M, ∃ u : Sˣ, f m = (u : S) • n) :
    IsNoetherian S N := by
  apply isNoetherian_of_left_inv_smul_mem_range f
  intro n
  obtain ⟨m, u, hm⟩ := hunit n
  exact ⟨m, (u : S), (↑(u⁻¹) : S), u.inv_mul, hm⟩

/-- Noetherianity ascends along a function-surjective semilinear map, without
requiring surjectivity of its scalar homomorphism. This generalizes Mathlib's
`isNoetherian_of_surjective`, whose range formulation uses that extra class. -/
theorem isNoetherian_of_surjective_semilinear (f : M →ₛₗ[φ] N)
    (hf : Function.Surjective f) [IsNoetherian R M] : IsNoetherian S N := by
  apply isNoetherian_of_unit_smul_mem_range f
  intro n
  obtain ⟨m, hm⟩ := hf n
  exact ⟨m, 1, by simpa only [Units.val_one, one_smul] using hm⟩

/-- When the scalar homomorphism is surjective, left-invertible scalar clearing
is equivalent to surjectivity of the semilinear map. This identifies the clearing
criterion with the range hypothesis in Mathlib's `isNoetherian_of_surjective`. -/
theorem LinearMap.range_eq_top_iff_left_inv_smul_mem_range [RingHomSurjective φ]
    (f : M →ₛₗ[φ] N) :
    LinearMap.range f = ⊤ ↔
      ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n := by
  rw [LinearMap.range_eq_top]
  constructor
  · intro hf n
    obtain ⟨m, hm⟩ := hf n
    exact ⟨m, 1, 1, one_mul 1, by simpa only [one_smul] using hm⟩
  · intro hclear n
    obtain ⟨m, a, b, hba, hm⟩ := hclear n
    obtain ⟨r, hr⟩ := RingHomSurjective.is_surjective (σ := φ) b
    refine ⟨r • m, ?_⟩
    rw [f.map_smulₛₗ, hr, hm, ← mul_smul, hba, one_smul]

end Module

/-- Surjectivity implies that each target element can be cleared into the image
by left multiplication by a unit. -/
theorem RingHom.exists_unit_mul_mem_range_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) (s : S) :
    ∃ u : Sˣ, (u : S) * s ∈ Set.range f := by
  refine ⟨1, ?_⟩
  simpa using hf s

/-- If every target element can be multiplied on the left by a unit into the
image, extension of the contraction recovers every left ideal. -/
theorem Ideal.map_comap_eq_of_unit_mul_mem_range (f : R →+* S)
    (h : ∀ s : S, ∃ u : Sˣ, (u : S) * s ∈ Set.range f) (I : Ideal S) :
    (I.comap f).map f = I := by
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  obtain ⟨u, y, hy⟩ := h x
  have hyI : y ∈ I.comap f := by
    apply Ideal.mem_comap.mpr
    rw [hy]
    exact I.mul_mem_left _ hx
  apply (Ideal.unit_mul_mem_iff_mem _ u.isUnit).mp
  rw [← hy]
  exact Ideal.mem_map_of_mem f hyI

/-- Left Noetherianity passes along a semiring homomorphism when every target
element can be multiplied on the left by a unit into its image. -/
theorem isNoetherianRing_of_unit_mul_mem_range (f : R →+* S)
    (h : ∀ s : S, ∃ u : Sˣ, (u : S) * s ∈ Set.range f) [IsNoetherianRing R] :
    IsNoetherianRing S := by
  apply isNoetherianRing_iff.mpr
  apply isNoetherian_of_unit_smul_mem_range f.toSemilinearMap
  intro s
  obtain ⟨u, r, hr⟩ := h s
  exact ⟨r, u, hr⟩

end Semiring

/-- Semilinear maps from a finitely generated semimodule to a Noetherian module
form a Noetherian module for the canonical pointwise action of a ring whose
codomain action commutes with the semilinear target scalars. This generalizes
Mathlib's `isNoetherian_linearMap`; the scalar homomorphism need not be surjective. -/
theorem isNoetherian_semilinearMap
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring R₂] [Ring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R₂ N] [Module S N] (σ : R →+* R₂)
    [SMulCommClass R₂ S N] [Module.Finite R M] [IsNoetherian S N] :
    IsNoetherian S (M →ₛₗ[σ] N) := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup S (M := N)
  obtain ⟨n, _v, ev, _hv, _hev, hinj⟩ :=
    LinearMap.exists_fin_injective_eval (S := S) (M := M) (N := N) σ
  have : IsNoetherian S (Fin n → N) := inferInstance
  exact isNoetherian_of_injective ev hinj

/-- Linear maps from a finitely generated `R`-semimodule to a Noetherian `S`-module
are Noetherian for the canonical pointwise `S`-action when the two codomain actions
commute. This is the identity-hom specialization of `isNoetherian_semilinearMap`. -/
theorem isNoetherian_linearMap_of_finite
    {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Ring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S N] [SMulCommClass R S N]
    [Module.Finite R M] [IsNoetherian S N] :
    IsNoetherian S (M →ₗ[R] N) :=
  isNoetherian_semilinearMap (RingHom.id R)

/-- Over a commutative ring, the commuting-action Hom theorem recovers Mathlib's
`isNoetherian_linearMap`, with the same pointwise scalar action and argument order.
The pointwise action is characterized by `LinearMap.smul_apply`. -/
private theorem isNoetherian_linearMap_commRing
    (R : Type uR) (M : Type uM) (N : Type uN)
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [IsNoetherian R M] [Module.Finite R N] : IsNoetherian R (N →ₗ[R] M) :=
  isNoetherian_linearMap_of_finite (R := R) (S := R) (M := N) (N := M)

section Ring

/-- If `M` is Noetherian over a ring `A` and finitely generated over a semiring `C`
whose given action commutes with the given `A`-action, then `A` modulo the annihilator
of its original action is left Noetherian. No Noetherianity assumption on `A` or `C`
is required. -/
theorem isNoetherianRing_quotient_annihilator_of_finite
    {A : Type uR} {C : Type uS} {M : Type uM}
    [Ring A] [Semiring C] [AddCommMonoid M]
    [Module A M] [Module C M] [SMulCommClass A C M]
    [Module.Finite C M] [IsNoetherian A M] :
    IsNoetherianRing (A ⧸ Module.annihilator A M) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup A (M := M)
  let : SMulCommClass C A M := SMulCommClass.symm A C M
  let : IsNoetherian A (M →ₗ[C] M) :=
    isNoetherian_linearMap_of_finite (R := C) (S := A)
  let f : A →ₗ[A] (M →ₗ[C] M) :=
    LinearMap.toSpanSingleton A (M →ₗ[C] M) (LinearMap.id : M →ₗ[C] M)
  let : IsNoetherian A (LinearMap.range f) :=
    isNoetherian_of_injective (LinearMap.range f).subtype Subtype.val_injective
  have hker : LinearMap.ker f = (Module.annihilator A M : Submodule A A) := by
    ext a
    constructor
    · intro ha
      apply Module.mem_annihilator.mpr
      intro m
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp ha) m
    · intro ha
      apply LinearMap.mem_ker.mpr
      ext m
      exact (Module.mem_annihilator.mp ha) m
  have hquot : IsNoetherian A (A ⧸ Module.annihilator A M) := by
    rw [← hker]
    exact f.quotKerEquivRange.isNoetherian_iff.mpr inferInstance
  exact isNoetherian_of_tower A hquot

/-- If the given scalar actions of a ring on a Noetherian module commute, the quotient
by the module's annihilator is left Noetherian. No Noetherianity assumption on the
scalar ring is required. -/
theorem isNoetherianRing_quotient_annihilator
    {A : Type uR} [Ring A] (X : Type uM) [AddCommGroup X] [Module A X]
    [SMulCommClass A A X] [IsNoetherian A X] :
    IsNoetherianRing (A ⧸ Module.annihilator A X) :=
  isNoetherianRing_quotient_annihilator_of_finite (A := A) (C := A) (M := X)

/-- A finitely generated module over a ring is Noetherian if the scalar ring modulo
its annihilator is left Noetherian. Only an additive commutative monoid is required
on the module; the given scalar actions need not commute. -/
theorem isNoetherian_of_finite_of_isNoetherianRing_quotient_annihilator
    {R : Type uR} {M : Type uM} [Ring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [IsNoetherianRing (R ⧸ Module.annihilator R M)] :
    IsNoetherian R M := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  let I := Module.annihilator R M
  let Q := R ⧸ I
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let ρ : R →+* Q := Ideal.Quotient.mk I
  -- Compare the two scalar structures only on the quotient ring.
  let l : Q →ₛₗ[ρ] Q :=
    (I : Submodule R R).liftQ ρ.toSemilinearMap (by
      intro r hr
      change Ideal.Quotient.mk I r = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hl (q : Q) : l q = q := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) q
    rfl
  let : IsNoetherian R Q :=
    (l.isNoetherian_iff_of_bijective
      ⟨fun a b hab ↦ (hl a).symm.trans (hab.trans (hl b)), fun q ↦ ⟨q, hl q⟩⟩).mpr
        inferInstance
  let : IsNoetherian R (Fin n → Q) := inferInstance
  let g : Fin n → Q →ₗ[R] M := fun i ↦
    (I : Submodule R R).liftQ (LinearMap.toSpanSingleton R M (x i)) (by
      intro r hr
      change r • x i = 0
      exact (Module.mem_annihilator.mp hr) (x i))
  -- Natural-number scalars give the aggregation without scalar-commutation assumptions on R.
  let f : (Fin n → Q) →ₗ[R] M := LinearMap.lsum R (fun _ : Fin n ↦ Q) ℕ g
  have hf (i : Fin n) : f (Pi.single i (ρ 1)) = x i := by
    rw [show f = LinearMap.lsum R (fun _ : Fin n ↦ Q) ℕ g from rfl,
      LinearMap.lsum_piSingle]
    change (LinearMap.toSpanSingleton R M (x i)) 1 = x i
    exact LinearMap.toSpanSingleton_apply_one (R := R) (M := M) (x i)
  have hrange : LinearMap.range f = ⊤ := by
    apply top_unique
    rw [← hx]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range.mpr ⟨Pi.single i (ρ 1), hf i⟩
  exact isNoetherian_of_surjective_semilinear f (LinearMap.range_eq_top.mp hrange)

/-- A module over a ring whose given scalar actions commute is Noetherian if and only if
it is finitely generated and its scalar ring modulo its annihilator is left Noetherian. -/
theorem isNoetherian_iff_finite_and_isNoetherianRing_quotient_annihilator
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [SMulCommClass R R M] :
    IsNoetherian R M ↔
      Module.Finite R M ∧ IsNoetherianRing (R ⧸ Module.annihilator R M) := by
  constructor
  · intro h
    let : IsNoetherian R M := h
    exact ⟨inferInstance, isNoetherianRing_quotient_annihilator (A := R) M⟩
  · rintro ⟨hfinite, hquot⟩
    let : Module.Finite R M := hfinite
    let : IsNoetherianRing (R ⧸ Module.annihilator R M) := hquot
    exact isNoetherian_of_finite_of_isNoetherianRing_quotient_annihilator (R := R) (M := M)

end Ring

section CommRing

namespace Ideal

/-- On a Noetherian module, containment of radicals after adding the annihilator
gives a uniform ideal-power bound. No Noetherianity assumption on the scalar ring,
or finite generation assumption on either original ideal, is required. -/
theorem exists_pow_smul_top_le_of_radical_sup_annihilator_le
    {R : Type uR} [CommRing R]
    {M : Type uM} [AddCommGroup M] [Module R M] {I J : Ideal R}
    [IsNoetherian R M]
    (h : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) ≤ J • ⊤ := by
  let := isNoetherianRing_quotient_annihilator (A := R) M
  exact exists_pow_smul_top_le_of_radical_sup_annihilator_le_of_map_fg
    (IsNoetherian.noetherian _) h

end Ideal

end CommRing
