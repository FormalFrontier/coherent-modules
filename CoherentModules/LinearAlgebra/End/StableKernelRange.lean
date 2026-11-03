/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Stable kernels and ranges of endomorphisms

Let `R` be a possibly noncommutative semiring and let `M` be an additive
commutative group with its given `R`-module structure. Simultaneous one-step
stability of the kernel and range of `f ^ n` gives the sum equivalence
`ker (f ^ n) × range (f ^ n) ≃ₗ[R] M`. The restricted endomorphisms are
nilpotent and invertible, respectively. The projections do not depend on the
stable bound and commute with arbitrary linear intertwiners.

The bound may be zero. Kernel and range are the particular negation-closed
submodules used here; arbitrary submodules over a semiring need not be
negation-closed. No scalar-module structure on a general linear Hom space is
used.

## References

Robert Wisbauer, *Foundations of Module and Ring Theory: A Handbook for Study
and Research*, Gordon and Breach, 1991, §31.13 (Fitting's lemma);
[author's text](https://www.math.uni-duesseldorf.de/~wisbauer/book.pdf).
The cited result decomposes an Artinian and Noetherian module over a ring.
The explicit one-step stability core here generalizes that ring-module setting
to semiring scalars and additive-group carriers, without global chain conditions.
The coordinate, projection and naturality API is developed for this broader
setting; the reference is not claimed to state this semiring generalization.

The Lean proofs reuse Mathlib's APIs. The chain-stability inputs and the Artinian
injectivity criterion come from
`Mathlib.RingTheory.Noetherian.Defs` and `Mathlib.RingTheory.Artinian.Module`.
The ring-scalar sum equivalence is compatible with
`Submodule.prodEquivOfIsCompl` from `Mathlib.LinearAlgebra.Projection`.
-/

@[expose] public section

universe uR uM uN uP

namespace LinearMap

section Kernel

variable {R : Type uR} [Semiring R] {S : Type*} [Semiring S]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module S N]
variable {σ : R →+* S}

/-- The stock linear kernel and additive-hom kernel have the same zero-kernel condition. -/
theorem ker_eq_bot_iff_addMonoidHom_ker_eq_bot (f : M →ₛₗ[σ] N) :
    f.ker = ⊥ ↔ f.toAddMonoidHom.ker = ⊥ := by
  constructor
  · intro h
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ f.ker := hx
    rw [h] at hx'
    exact hx'
  · intro h
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ f.toAddMonoidHom.ker := hx
    rw [h] at hx'
    exact hx'

/-- The kernel criterion for injectivity only needs semiring scalars and a group domain.
For ring scalars and group codomain, this specializes to `LinearMap.ker_eq_bot`. -/
theorem ker_eq_bot_of_semiring (f : M →ₛₗ[σ] N) :
    f.ker = ⊥ ↔ Function.Injective f :=
  (ker_eq_bot_iff_addMonoidHom_ker_eq_bot f).trans f.toAddMonoidHom.ker_eq_bot_iff

/-- This particular kernel is negation-closed even for semiring scalars. -/
theorem neg_mem_ker_of_semiring (f : M →ₛₗ[σ] N) {x : M} (hx : x ∈ f.ker) :
    -x ∈ f.ker :=
  f.toAddMonoidHom.ker.neg_mem hx

end Kernel

section Range

variable {R : Type uR} [Semiring R] {S : Type*} [Semiring S]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module S N]
variable {σ : R →+* S} [RingHomSurjective σ]

/-- This particular range is negation-closed even for semiring scalars. -/
theorem neg_mem_range_of_semiring (f : M →ₛₗ[σ] N) {x : N} (hx : x ∈ f.range) :
    -x ∈ f.range :=
  f.toAddMonoidHom.range.neg_mem hx

end Range

end LinearMap

namespace Module.End

section AddCommMonoid

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- Noetherianity and Artinianity of the module give a common one-step stable bound.
This is the chain-stability input to the classical Fitting lemma (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13). Bound existence here allows
semiring scalars and additive-monoid carriers. -/
theorem exists_stable_ker_range [IsNoetherian R M] [IsArtinian R M]
    (f : Module.End R M) :
    ∃ n : ℕ, LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)) ∧
      LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)) := by
  obtain ⟨a, ha : ∀ m, a ≤ m → LinearMap.ker (f ^ a) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  obtain ⟨b, hb : ∀ m, b ≤ m → LinearMap.range (f ^ b) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine ⟨max a b, ?_, ?_⟩
  · exact (ha _ (Nat.le_max_left a b)).symm.trans
      (ha _ ((Nat.le_max_left a b).trans (Nat.le_succ _)))
  · exact (hb _ (Nat.le_max_right a b)).symm.trans
      (hb _ ((Nat.le_max_right a b).trans (Nat.le_succ _)))

/-- The automorphism induced by an injective endomorphism of an Artinian semimodule. -/
noncomputable def equivOfInjectiveOfIsArtinian [IsArtinian R M]
    (f : Module.End R M) (hf : Function.Injective f) : M ≃ₗ[R] M :=
  { f with
    invFun := @Function.invFun M M ⟨0⟩ f
    left_inv := Function.leftInverse_invFun hf
    right_inv := Function.rightInverse_invFun
      (IsArtinian.surjective_of_injective_endomorphism f hf) }

@[simp]
theorem equivOfInjectiveOfIsArtinian_apply [IsArtinian R M]
    (f : Module.End R M) (hf : Function.Injective f) (x : M) :
    equivOfInjectiveOfIsArtinian f hf x = f x := rfl

@[simp]
theorem equivOfInjectiveOfIsArtinian_symm_apply [IsArtinian R M]
    (f : Module.End R M) (hf : Function.Injective f) (x : M) :
    (equivOfInjectiveOfIsArtinian f hf).symm x =
      @Function.invFun M M ⟨0⟩ f x := rfl

/-- Restriction of an endomorphism to the kernel of a power. -/
def kerPowRestrict (f : Module.End R M) (n : ℕ) :
    Module.End R (LinearMap.ker (f ^ n)) :=
  f.restrict (by
    intro x hx
    change (f ^ n) (f x) = 0
    rw [← mul_apply, ← pow_succ, pow_succ', mul_apply]
    simpa only [map_zero] using congrArg f (show (f ^ n) x = 0 from hx))

/-- Restriction of an endomorphism to the range of a power. -/
def rangePowRestrict (f : Module.End R M) (n : ℕ) :
    Module.End R (LinearMap.range (f ^ n)) :=
  f.restrict (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨f y, ?_⟩
    rw [← mul_apply, ← pow_succ, pow_succ', mul_apply])

@[simp]
theorem kerPowRestrict_apply (f : Module.End R M) (n : ℕ)
    (x : LinearMap.ker (f ^ n)) : (kerPowRestrict f n x : M) = f x := rfl

@[simp]
theorem rangePowRestrict_apply (f : Module.End R M) (n : ℕ)
    (x : LinearMap.range (f ^ n)) : (rangePowRestrict f n x : M) = f x := rfl

/-- The restriction to the kernel of the nth power has nth power zero, including `n = 0`. -/
theorem kerPowRestrict_pow (f : Module.End R M) (n : ℕ) :
    kerPowRestrict f n ^ n = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hker : ∀ y ∈ LinearMap.ker (f ^ n), f y ∈ LinearMap.ker (f ^ n) :=
    fun y hy => (kerPowRestrict f n ⟨y, hy⟩).property
  simpa only [kerPowRestrict, Module.End.pow_restrict n hker,
    LinearMap.coe_restrict_apply, LinearMap.zero_apply, Submodule.coe_zero] using
      (show (f ^ n) (x : M) = 0 from x.property)

/-- Kernel one-step stability propagates to every later power.
This is the semiring form of `Module.End.ker_pow_constant`. -/
theorem ker_pow_eq_of_stable (f : Module.End R M) (n : ℕ)
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (m : ℕ) (hm : n ≤ m) :
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      LinearMap.ker (f ^ (n + (k + 1))) =
          (LinearMap.ker (f ^ (n + k))).comap f := by
        rw [← Nat.add_assoc, pow_succ, mul_eq_comp, LinearMap.ker_comp]
      _ = (LinearMap.ker (f ^ n)).comap f := by rw [ih]
      _ = LinearMap.ker (f ^ (n + 1)) := by
        rw [pow_succ, mul_eq_comp, LinearMap.ker_comp]
      _ = LinearMap.ker (f ^ n) := hK.symm

/-- The offset-indexed form of kernel stability over semiring scalars.
Its division-ring specialization has the exact conclusion of `Module.End.ker_pow_constant`. -/
theorem ker_pow_constant_of_semiring (f : Module.End R M) (n : ℕ)
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1))) :
    ∀ m : ℕ, LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + m)) :=
  fun m ↦ (ker_pow_eq_of_stable f n hK (n + m) (Nat.le_add_right n m)).symm

/-- Range one-step stability propagates to every later power. -/
theorem range_pow_eq_of_stable (f : Module.End R M) (n : ℕ)
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    (m : ℕ) (hm : n ≤ m) :
    LinearMap.range (f ^ m) = LinearMap.range (f ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      LinearMap.range (f ^ (n + (k + 1))) =
          (LinearMap.range (f ^ (n + k))).map f := by
        rw [← Nat.add_assoc, pow_succ', mul_eq_comp, LinearMap.range_comp]
      _ = (LinearMap.range (f ^ n)).map f := by rw [ih]
      _ = LinearMap.range (f ^ (n + 1)) := by
        rw [pow_succ', mul_eq_comp, LinearMap.range_comp]
      _ = LinearMap.range (f ^ n) := hI.symm

/-- Both one-step equalities hold at every later bound. -/
theorem stable_at_of_stable (f : Module.End R M) (n : ℕ)
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    (m : ℕ) (hm : n ≤ m) :
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (m + 1)) ∧
      LinearMap.range (f ^ m) = LinearMap.range (f ^ (m + 1)) := by
  exact ⟨(ker_pow_eq_of_stable f n hK m hm).trans
      (ker_pow_eq_of_stable f n hK (m + 1) (hm.trans (Nat.le_succ m))).symm,
    (range_pow_eq_of_stable f n hI m hm).trans
      (range_pow_eq_of_stable f n hI (m + 1) (hm.trans (Nat.le_succ m))).symm⟩

/-- Stable power kernels and ranges are independent of the chosen stable bound. -/
theorem stable_submodules_eq (f : Module.End R M) (n : ℕ)
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    (m : ℕ) (hKm : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (m + 1)))
    (hIm : LinearMap.range (f ^ m) = LinearMap.range (f ^ (m + 1))) :
    LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m) ∧
      LinearMap.range (f ^ n) = LinearMap.range (f ^ m) := by
  exact ⟨(ker_pow_eq_of_stable f n hK (max n m) (Nat.le_max_left n m)).symm.trans
      (ker_pow_eq_of_stable f m hKm (max n m) (Nat.le_max_right n m)),
    (range_pow_eq_of_stable f n hI (max n m) (Nat.le_max_left n m)).symm.trans
      (range_pow_eq_of_stable f m hIm (max n m) (Nat.le_max_right n m))⟩

/-- An intertwiner maps a power kernel into any stable target kernel. -/
theorem mapsTo_ker_pow_of_intertwines_of_stable (f : Module.End R M) (n : ℕ)
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (g : Module.End R N) (m : ℕ) (h : M →ₗ[R] N) (hh : h.comp f = g.comp h)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1))) :
    Set.MapsTo h (LinearMap.ker (f ^ n)) (LinearMap.ker (g ^ m)) := by
  intro x hx
  rw [← ker_pow_eq_of_stable g m hKg (max n m) (Nat.le_max_right n m)]
  change (g ^ (max n m)) (h x) = 0
  calc
    (g ^ (max n m)) (h x) = h ((f ^ (max n m)) x) :=
      LinearMap.congr_fun (commute_pow_left_of_commute hh.symm (max n m)) x
    _ = 0 := by
      rw [pow_map_zero_of_le (Nat.le_max_left n m) (show (f ^ n) x = 0 from hx),
        map_zero]

/-- An intertwiner maps a stable source range into every target power range. -/
theorem mapsTo_range_pow_of_intertwines_of_stable (f : Module.End R M) (n : ℕ)
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (g : Module.End R N) (m : ℕ) (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) :
    Set.MapsTo h (LinearMap.range (f ^ n)) (LinearMap.range (g ^ m)) := by
  intro x hx
  have hx' : x ∈ LinearMap.range (f ^ (max n m)) := by
    rw [range_pow_eq_of_stable f n hI (max n m) (Nat.le_max_left n m)]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  apply g.iterateRange.monotone (Nat.le_max_right n m)
  exact ⟨h y, LinearMap.congr_fun
    (commute_pow_left_of_commute hh.symm (max n m)) y⟩

section Intertwiner

variable (f : Module.End R M) (n : ℕ)
variable (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
variable (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {P : Type uP} [AddCommMonoid P] [Module R P]

/-- An intertwiner carries a power kernel into a stable target kernel. -/
def kerPowIntertwiner (g : Module.End R N) (m : ℕ) (h : M →ₗ[R] N)
    (hh : h.comp f = g.comp h)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1))) :
    LinearMap.ker (f ^ n) →ₗ[R] LinearMap.ker (g ^ m) :=
  h.restrict (mapsTo_ker_pow_of_intertwines_of_stable f n g m h hh hKg)

/-- An intertwiner carries a stable source range into a power range. -/
def rangePowIntertwiner
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    (g : Module.End R N) (m : ℕ) (h : M →ₗ[R] N)
    (hh : h.comp f = g.comp h) :
    LinearMap.range (f ^ n) →ₗ[R] LinearMap.range (g ^ m) :=
  h.restrict (mapsTo_range_pow_of_intertwines_of_stable f n hI g m h hh)

@[simp]
theorem kerPowIntertwiner_apply (g : Module.End R N) (m : ℕ) (h : M →ₗ[R] N)
    (hh : h.comp f = g.comp h)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (x : LinearMap.ker (f ^ n)) :
    (kerPowIntertwiner f n g m h hh hKg x : N) = h x := rfl

@[simp]
theorem rangePowIntertwiner_apply (g : Module.End R N) (m : ℕ) (h : M →ₗ[R] N)
    (hh : h.comp f = g.comp h) (x : LinearMap.range (f ^ n)) :
    (rangePowIntertwiner f n hI g m h hh x : N) = h x := rfl

@[simp]
theorem kerPowIntertwiner_id :
    kerPowIntertwiner f n f n LinearMap.id (by ext x; rfl) hK = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem rangePowIntertwiner_id :
    rangePowIntertwiner f n hI f n LinearMap.id (by ext x; rfl) = LinearMap.id := by
  ext x
  rfl

/-- Restriction to stable kernels respects composition of intertwiners. -/
theorem kerPowIntertwiner_comp (g : Module.End R N) (m : ℕ)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (q : Module.End R P) (l : ℕ)
    (hKq : LinearMap.ker (q ^ l) = LinearMap.ker (q ^ (l + 1)))
    (h₁ : M →ₗ[R] N) (hh₁ : h₁.comp f = g.comp h₁)
    (h₂ : N →ₗ[R] P) (hh₂ : h₂.comp g = q.comp h₂) :
    kerPowIntertwiner f n q l (h₂.comp h₁) (by
        simpa only [LinearMap.comp_assoc, hh₁] using
          congrArg (fun t => t.comp h₁) hh₂) hKq =
      (kerPowIntertwiner g m q l h₂ hh₂ hKq).comp
        (kerPowIntertwiner f n g m h₁ hh₁ hKg) := by
  ext x
  rfl

/-- Restriction to stable ranges respects composition of intertwiners. -/
theorem rangePowIntertwiner_comp (g : Module.End R N) (m : ℕ)
    (hIg : LinearMap.range (g ^ m) = LinearMap.range (g ^ (m + 1)))
    (q : Module.End R P) (l : ℕ)
    (h₁ : M →ₗ[R] N) (hh₁ : h₁.comp f = g.comp h₁)
    (h₂ : N →ₗ[R] P) (hh₂ : h₂.comp g = q.comp h₂) :
    rangePowIntertwiner f n hI q l (h₂.comp h₁) (by
        simpa only [LinearMap.comp_assoc, hh₁] using
          congrArg (fun t => t.comp h₁) hh₂) =
      (rangePowIntertwiner g m hIg q l h₂ hh₂).comp
        (rangePowIntertwiner f n hI g m h₁ hh₁) := by
  ext x
  rfl

/-- Nilpotent and invertible invariant summands identify the stable kernel and range.
This characterizes the summands of the classical Fitting decomposition (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13). Unlike the cited ring-module
setting, this uniqueness statement allows semiring scalars and additive-monoid
carriers, with explicit one-step stability. -/
theorem fittingSummands_unique
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    (P Q : Submodule R M)
    (hP : ∀ x ∈ P, f x ∈ P) (hQ : ∀ x ∈ Q, f x ∈ Q)
    (hsup : P ⊔ Q = ⊤) (hNil : IsNilpotent (f.restrict hP : Module.End R P))
    (hBij : Function.Bijective (f.restrict hQ : Module.End R Q)) :
    P = LinearMap.ker (f ^ n) ∧ Q = LinearMap.range (f ^ n) := by
  obtain ⟨a, ha⟩ := hNil
  let l := max n a
  have hPa (x : M) (hx : x ∈ P) : (f ^ a) x = 0 := by
    have hp := LinearMap.congr_fun ha (⟨x, hx⟩ : P)
    simpa only [Module.End.pow_restrict a hP, LinearMap.coe_restrict_apply,
      LinearMap.zero_apply, Submodule.coe_zero] using
        congrArg (fun y : P => (y : M)) hp
  have hPl (x : M) (hx : x ∈ P) : (f ^ l) x = 0 :=
    pow_map_zero_of_le (Nat.le_max_right n a) (hPa x hx)
  have hPK : P ≤ LinearMap.ker (f ^ n) := by
    intro x hx
    rw [← ker_pow_eq_of_stable f n hK l (Nat.le_max_left n a)]
    exact hPl x hx
  have hQI : Q ≤ LinearMap.range (f ^ n) := by
    intro x hx
    obtain ⟨y, hy⟩ := (iterate_bijective hBij n).surjective (⟨x, hx⟩ : Q)
    refine ⟨(y : M), ?_⟩
    simpa only [Module.End.pow_restrict n hQ, LinearMap.coe_restrict_apply] using
      congrArg (fun z : Q => (z : M)) hy
  have hKP : LinearMap.ker (f ^ n) ≤ P := by
    intro x hx
    have hxl : (f ^ l) x = 0 :=
      pow_map_zero_of_le (Nat.le_max_left n a) (show (f ^ n) x = 0 from hx)
    have hxSup : x ∈ P ⊔ Q := by rw [hsup]; trivial
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hxSup
    have hql : (f ^ l) q = 0 := by
      rw [← hpq, map_add, hPl p hp, zero_add] at hxl
      exact hxl
    have hqzero : (⟨q, hq⟩ : Q) = 0 := by
      apply (iterate_bijective hBij l).injective
      apply Subtype.ext
      simpa only [Module.End.pow_restrict l hQ, LinearMap.coe_restrict_apply,
        map_zero, Submodule.coe_zero] using hql
    have hqzero' : q = 0 := congrArg (fun y : Q => (y : M)) hqzero
    rw [← hpq, hqzero', add_zero]
    exact hp
  have hIQ : LinearMap.range (f ^ n) ≤ Q := by
    intro x hx
    have hxl : x ∈ LinearMap.range (f ^ l) := by
      rw [range_pow_eq_of_stable f n hI l (Nat.le_max_left n a)]
      exact hx
    obtain ⟨z, rfl⟩ := hxl
    have hzSup : z ∈ P ⊔ Q := by rw [hsup]; trivial
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hzSup
    rw [← hpq, map_add, hPl p hp, zero_add]
    exact pow_apply_mem_of_forall_mem l hQ q hq
  exact ⟨le_antisymm hPK hKP, le_antisymm hQI hIQ⟩

/-- The component maps intertwine the two restricted endomorphisms. -/
theorem fittingRestrictions_natural (g : Module.End R N) (m : ℕ)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) :
    (kerPowIntertwiner f n g m h hh hKg).comp (kerPowRestrict f n) =
        (kerPowRestrict g m).comp (kerPowIntertwiner f n g m h hh hKg) ∧
      (rangePowIntertwiner f n hI g m h hh).comp (rangePowRestrict f n) =
        (rangePowRestrict g m).comp (rangePowIntertwiner f n hI g m h hh) := by
  constructor
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hh (x : M)
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hh (x : M)

end Intertwiner

end AddCommMonoid

section AddCommGroup

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

variable (f : Module.End R M) (n : ℕ)
variable (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
variable (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))

/-- Simultaneous one-step stability makes the specified kernel and range complementary.
This generalizes the complementarity in the classical Fitting lemma (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13) from Artinian and Noetherian
ring-modules to semiring scalars and additive-group carriers at an explicit
one-step stable bound. -/
theorem isCompl_ker_pow_range_pow_of_stable
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1))) :
    IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hxK hxI
    obtain ⟨y, rfl⟩ := hxI
    have hy : y ∈ LinearMap.ker (f ^ (n + n)) := by
      change (f ^ (n + n)) y = 0
      rw [pow_add, mul_apply]
      exact hxK
    rw [ker_pow_eq_of_stable f n hK (n + n) (Nat.le_add_right n n)] at hy
    exact hy
  · rw [codisjoint_iff_le_sup]
    intro x _
    have hx : (f ^ n) x ∈ LinearMap.range (f ^ (n + n)) := by
      rw [range_pow_eq_of_stable f n hI (n + n) (Nat.le_add_right n n)]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx
    have hy' : (f ^ n) ((f ^ n) y) = (f ^ n) x := by
      simpa only [pow_add, mul_apply] using hy
    have hk : x - (f ^ n) y ∈ LinearMap.ker (f ^ n) := by
      rw [LinearMap.mem_ker, map_sub, hy', sub_self]
    have hi : (f ^ n) y ∈ LinearMap.range (f ^ n) := ⟨y, rfl⟩
    simpa only [sub_add_cancel] using Submodule.add_mem_sup hk hi

/-- Under one-step stability, addition from the power kernel and range is bijective.
This is the sum-map form of the Fitting decomposition (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13), generalized here from
ring-modules to semiring scalars and additive-group carriers under explicit
one-step stability. -/
theorem bijective_ker_range_coprod_of_stable
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1))) :
    Function.Bijective
      ((LinearMap.ker (f ^ n)).subtype.coprod (LinearMap.range (f ^ n)).subtype) := by
  have hc := isCompl_ker_pow_range_pow_of_stable f n hK hI
  constructor
  · rintro ⟨k₁, i₁⟩ ⟨k₂, i₂⟩ h
    change (k₁ : M) + (i₁ : M) = (k₂ : M) + (i₂ : M) at h
    have hk : (k₁ : M) - (k₂ : M) ∈ LinearMap.ker (f ^ n) := by
      change (f ^ n) ((k₁ : M) - (k₂ : M)) = 0
      rw [map_sub, k₁.property, k₂.property, sub_self]
    have hdiff : (k₁ : M) - (k₂ : M) = (i₂ : M) - (i₁ : M) :=
      sub_eq_sub_iff_add_eq_add.mpr (h.trans (add_comm _ _))
    have hi : (k₁ : M) - (k₂ : M) ∈ LinearMap.range (f ^ n) := by
      rw [hdiff, sub_eq_add_neg]
      exact (LinearMap.range (f ^ n)).add_mem i₂.property
        (LinearMap.neg_mem_range_of_semiring (f ^ n) i₁.property)
    have hkeq : k₁ = k₂ :=
      Subtype.ext (sub_eq_zero.mp (Submodule.disjoint_def.mp hc.disjoint _ hk hi))
    refine Prod.ext hkeq (Subtype.ext ?_)
    rw [hkeq] at h
    exact add_left_cancel h
  · rw [← LinearMap.range_eq_top, ← Submodule.sup_eq_range, hc.sup_eq_top]

/-- The sum equivalence of a stable kernel and range. Its forward map is addition.
The classical ring-module antecedent is Fitting's lemma (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13). This construction instead uses
semiring scalars, additive-group carriers and an explicit one-step stable bound;
it does not require the global chain conditions of the cited result. -/
noncomputable def fittingEquiv
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1))) :
    (LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) ≃ₗ[R] M :=
  { (LinearMap.ker (f ^ n)).subtype.coprod (LinearMap.range (f ^ n)).subtype with
    invFun := @Function.invFun (LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) M
      ⟨(0, 0)⟩ ((LinearMap.ker (f ^ n)).subtype.coprod (LinearMap.range (f ^ n)).subtype)
    left_inv := Function.leftInverse_invFun
      (bijective_ker_range_coprod_of_stable f n hK hI).injective
    right_inv := Function.rightInverse_invFun
      (bijective_ker_range_coprod_of_stable f n hK hI).surjective }

@[simp]
theorem fittingEquiv_apply (x : LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) :
    fittingEquiv f n hK hI x = (x.1 : M) + (x.2 : M) := rfl

/-- The inverse is the fixed total inverse of the sum map. -/
theorem fittingEquiv_symm_apply (x : M) :
    (fittingEquiv f n hK hI).symm x =
      @Function.invFun (LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) M
        ⟨(0, 0)⟩ ((LinearMap.ker (f ^ n)).subtype.coprod
          (LinearMap.range (f ^ n)).subtype) x := rfl

@[simp]
theorem fittingEquiv_symm_apply_add (k : LinearMap.ker (f ^ n))
    (i : LinearMap.range (f ^ n)) :
    (fittingEquiv f n hK hI).symm ((k : M) + (i : M)) = (k, i) := by
  exact (fittingEquiv f n hK hI).symm_apply_apply (k, i)

/-- The kernel-valued component of the stable decomposition. -/
noncomputable def fittingKernelComponent : M →ₗ[R] LinearMap.ker (f ^ n) :=
  (LinearMap.fst R (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n))).comp
    (fittingEquiv f n hK hI).symm.toLinearMap

/-- The range-valued component of the stable decomposition. -/
noncomputable def fittingRangeComponent : M →ₗ[R] LinearMap.range (f ^ n) :=
  (LinearMap.snd R (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n))).comp
    (fittingEquiv f n hK hI).symm.toLinearMap

/-- The kernel component is the first inverse coordinate. -/
@[simp]
theorem fittingKernelComponent_apply (x : M) :
    fittingKernelComponent f n hK hI x = ((fittingEquiv f n hK hI).symm x).1 := rfl

/-- The range component is the second inverse coordinate. -/
@[simp]
theorem fittingRangeComponent_apply (x : M) :
    fittingRangeComponent f n hK hI x = ((fittingEquiv f n hK hI).symm x).2 := rfl

/-- The ambient projection onto the stable kernel. -/
noncomputable def fittingKernelProjection : Module.End R M :=
  (LinearMap.ker (f ^ n)).subtype.comp (fittingKernelComponent f n hK hI)

/-- The ambient projection onto the stable range. -/
noncomputable def fittingRangeProjection : Module.End R M :=
  (LinearMap.range (f ^ n)).subtype.comp (fittingRangeComponent f n hK hI)

/-- The restriction to a stable power range is bijective. -/
theorem bijective_rangePowRestrict_of_stable
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1))) :
    Function.Bijective (rangePowRestrict f n) := by
  have hc := isCompl_ker_pow_range_pow_of_stable f n hK hI
  constructor
  · intro x y h
    have hxy : f (x : M) = f (y : M) :=
      congrArg (fun z : LinearMap.range (f ^ n) => (z : M)) h
    have hk : (x : M) - (y : M) ∈ LinearMap.ker (f ^ (n + 1)) := by
      change (f ^ (n + 1)) ((x : M) - (y : M)) = 0
      rw [pow_succ, mul_apply, map_sub, hxy, sub_self, map_zero]
    have hk' : (x : M) - (y : M) ∈ LinearMap.ker (f ^ n) := by
      rw [hK]
      exact hk
    have hi : (x : M) - (y : M) ∈ LinearMap.range (f ^ n) := by
      rw [sub_eq_add_neg]
      exact (LinearMap.range (f ^ n)).add_mem x.property
        (LinearMap.neg_mem_range_of_semiring (f ^ n) y.property)
    exact Subtype.ext
      (sub_eq_zero.mp (Submodule.disjoint_def.mp hc.disjoint _ hk' hi))
  · intro y
    have hy : (y : M) ∈ LinearMap.range (f ^ (n + 1)) := by
      rw [← hI]
      exact y.property
    obtain ⟨z, hz⟩ := hy
    refine ⟨⟨(f ^ n) z, ⟨z, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change f ((f ^ n) z) = (y : M)
    simpa only [pow_succ', mul_apply] using hz

/-- The range restriction as an automorphism, with a fixed total inverse function.
This constructs the invertible part of the Fitting decomposition (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13) in the semiring/additive-group
setting under explicit one-step stability, rather than global chain conditions. -/
noncomputable def fittingRangeAut
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1))) :
    LinearMap.range (f ^ n) ≃ₗ[R] LinearMap.range (f ^ n) :=
  { rangePowRestrict f n with
    invFun := @Function.invFun (LinearMap.range (f ^ n)) (LinearMap.range (f ^ n))
      ⟨0⟩ (rangePowRestrict f n)
    left_inv := Function.leftInverse_invFun
      (bijective_rangePowRestrict_of_stable f n hK hI).injective
    right_inv := Function.rightInverse_invFun
      (bijective_rangePowRestrict_of_stable f n hK hI).surjective }

@[simp]
theorem fittingRangeAut_apply (x : LinearMap.range (f ^ n)) :
    (fittingRangeAut f n hK hI x : M) = f x := rfl

/-- The inverse of the range automorphism is fixed independently of the stability proofs. -/
theorem fittingRangeAut_symm_apply (x : LinearMap.range (f ^ n)) :
    (fittingRangeAut f n hK hI).symm x =
      @Function.invFun (LinearMap.range (f ^ n)) (LinearMap.range (f ^ n))
        ⟨0⟩ (rangePowRestrict f n) x := rfl

/-- The two inverse coordinates have the stated ambient projection values. -/
theorem fittingEquiv_symm_apply_coe (x : M) :
    (((fittingEquiv f n hK hI).symm x).1 : M) = fittingKernelProjection f n hK hI x ∧
      (((fittingEquiv f n hK hI).symm x).2 : M) = fittingRangeProjection f n hK hI x :=
  ⟨rfl, rfl⟩

/-- Evaluation of the kernel projection in the sum coordinates. -/
theorem fittingKernelProjection_apply_fittingEquiv
    (x : LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) :
    fittingKernelProjection f n hK hI (fittingEquiv f n hK hI x) = x.1 := by
  exact congrArg (fun y : LinearMap.ker (f ^ n) × LinearMap.range (f ^ n) =>
    (y.1 : M)) ((fittingEquiv f n hK hI).symm_apply_apply x)

/-- Evaluation of the range projection in the sum coordinates. -/
theorem fittingRangeProjection_apply_fittingEquiv
    (x : LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) :
    fittingRangeProjection f n hK hI (fittingEquiv f n hK hI x) = x.2 := by
  exact congrArg (fun y : LinearMap.ker (f ^ n) × LinearMap.range (f ^ n) =>
    (y.2 : M)) ((fittingEquiv f n hK hI).symm_apply_apply x)

/-- The kernel projection takes values in the specified power kernel. -/
theorem fittingKernelProjection_mem (x : M) :
    fittingKernelProjection f n hK hI x ∈ LinearMap.ker (f ^ n) :=
  (fittingKernelComponent f n hK hI x).property

/-- The range projection takes values in the specified power range. -/
theorem fittingRangeProjection_mem (x : M) :
    fittingRangeProjection f n hK hI x ∈ LinearMap.range (f ^ n) :=
  (fittingRangeComponent f n hK hI x).property

/-- The two ambient components reconstruct the input. -/
theorem fittingProjections_add_apply (x : M) :
    fittingKernelProjection f n hK hI x + fittingRangeProjection f n hK hI x = x := by
  exact (fittingEquiv f n hK hI).apply_symm_apply x

/-- The kernel component is the difference between the input and its range component. -/
theorem fittingKernelProjection_apply (x : M) :
    fittingKernelProjection f n hK hI x = x - fittingRangeProjection f n hK hI x := by
  exact (eq_sub_iff_add_eq).2 (fittingProjections_add_apply f n hK hI x)

/-- The range component is characterized by its power image. -/
theorem fittingRangeProjection_unique (x y : M) :
    y = fittingRangeProjection f n hK hI x ↔
      y ∈ LinearMap.range (f ^ n) ∧ (f ^ n) y = (f ^ n) x := by
  constructor
  · rintro rfl
    refine ⟨fittingRangeProjection_mem f n hK hI x, ?_⟩
    have hk := LinearMap.mem_ker.mp (fittingKernelProjection_mem f n hK hI x)
    have hs := congrArg (f ^ n) (fittingProjections_add_apply f n hK hI x)
    simpa only [map_add, hk, zero_add] using hs
  · rintro ⟨hy, hxy⟩
    let k : LinearMap.ker (f ^ n) := ⟨x - y, by
      simp only [LinearMap.mem_ker, map_sub, hxy, sub_self]⟩
    let i : LinearMap.range (f ^ n) := ⟨y, hy⟩
    have hs : fittingEquiv f n hK hI (k, i) = x := by
      exact sub_add_cancel x y
    have hi := fittingRangeProjection_apply_fittingEquiv f n hK hI (k, i)
    simpa only [hs] using hi.symm

/-- The range component is the inverse power-image lift within the stable range. -/
theorem fittingRangeProjection_apply_invFun (x : M) :
    fittingRangeProjection f n hK hI x =
      ((@Function.invFun (LinearMap.range (f ^ n)) (LinearMap.range (f ^ n))
        ⟨0⟩ (((f ^ n).rangeRestrict).domRestrict (LinearMap.range (f ^ n)))
        ((f ^ n).rangeRestrict x)) : M) := by
  let t := ((f ^ n).rangeRestrict).domRestrict (LinearMap.range (f ^ n))
  have ht : Function.Injective t := by
    intro a b hab
    apply Subtype.ext
    have ha := (fittingRangeProjection_unique f n hK hI (b : M) (a : M)).2
      ⟨a.property, congrArg (fun z : LinearMap.range (f ^ n) => (z : M)) hab⟩
    have hb := (fittingRangeProjection_unique f n hK hI (b : M) (b : M)).2
      ⟨b.property, rfl⟩
    exact ha.trans hb.symm
  let q := fittingRangeComponent f n hK hI x
  have hq : t q = (f ^ n).rangeRestrict x := by
    apply Subtype.ext
    exact ((fittingRangeProjection_unique f n hK hI x
      (fittingRangeProjection f n hK hI x)).1 rfl).2
  have hi := @Function.leftInverse_invFun (LinearMap.range (f ^ n))
    (LinearMap.range (f ^ n)) ⟨0⟩ t ht q
  rw [hq] at hi
  exact (congrArg (fun z : LinearMap.range (f ^ n) => (z : M)) hi).symm

/-- The sum formula uniquely determines the stable equivalence.
This specifies the addition equivalence for the Fitting decomposition (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13). The equivalence here is the
explicit-one-step semiring/additive-group generalization, not a claim that the
reference treats semiring scalars. -/
theorem fittingEquiv_unique
    (e : (LinearMap.ker (f ^ n) × LinearMap.range (f ^ n)) ≃ₗ[R] M)
    (he : ∀ x, e x = (x.1 : M) + (x.2 : M)) :
    fittingEquiv f n hK hI = e := by
  ext x
  exact (he x).symm

/-- Projection values on a sum of the specified summands. -/
theorem fittingProjections_apply_add (k : LinearMap.ker (f ^ n))
    (i : LinearMap.range (f ^ n)) :
    fittingKernelProjection f n hK hI ((k : M) + (i : M)) = k ∧
      fittingRangeProjection f n hK hI ((k : M) + (i : M)) = i := by
  exact ⟨fittingKernelProjection_apply_fittingEquiv f n hK hI (k, i),
    fittingRangeProjection_apply_fittingEquiv f n hK hI (k, i)⟩

theorem fittingKernelProjection_apply_of_mem_ker {x : M}
    (hx : x ∈ LinearMap.ker (f ^ n)) :
    fittingKernelProjection f n hK hI x = x := by
  simpa only [Submodule.coe_zero, add_zero] using
    (fittingProjections_apply_add f n hK hI ⟨x, hx⟩ 0).1

theorem fittingRangeProjection_apply_of_mem_range {x : M}
    (hx : x ∈ LinearMap.range (f ^ n)) :
    fittingRangeProjection f n hK hI x = x := by
  simpa only [Submodule.coe_zero, zero_add] using
    (fittingProjections_apply_add f n hK hI 0 ⟨x, hx⟩).2

theorem fittingKernelProjection_apply_of_mem_range {x : M}
    (hx : x ∈ LinearMap.range (f ^ n)) :
    fittingKernelProjection f n hK hI x = 0 := by
  simpa only [Submodule.coe_zero, zero_add] using
    (fittingProjections_apply_add f n hK hI 0 ⟨x, hx⟩).1

theorem fittingRangeProjection_apply_of_mem_ker {x : M}
    (hx : x ∈ LinearMap.ker (f ^ n)) :
    fittingRangeProjection f n hK hI x = 0 := by
  simpa only [Submodule.coe_zero, add_zero] using
    (fittingProjections_apply_add f n hK hI ⟨x, hx⟩ 0).2

-- Simplification uses the zero-equation normal form for kernel membership and
-- concrete power images for range membership. The membership lemmas above
-- remain available for explicit application.

/-- The kernel projection fixes an element annihilated by the stable power. -/
@[simp]
theorem fittingKernelProjection_apply_of_pow_eq_zero {x : M}
    (hx : (f ^ n) x = 0) :
    fittingKernelProjection f n hK hI x = x :=
  fittingKernelProjection_apply_of_mem_ker f n hK hI hx

/-- The range projection vanishes on an element annihilated by the stable power. -/
@[simp]
theorem fittingRangeProjection_apply_of_pow_eq_zero {x : M}
    (hx : (f ^ n) x = 0) :
    fittingRangeProjection f n hK hI x = 0 :=
  fittingRangeProjection_apply_of_mem_ker f n hK hI hx

/-- The kernel projection vanishes on an image of the stable power. -/
@[simp]
theorem fittingKernelProjection_apply_pow (x : M) :
    fittingKernelProjection f n hK hI ((f ^ n) x) = 0 :=
  fittingKernelProjection_apply_of_mem_range f n hK hI ⟨x, rfl⟩

/-- The range projection fixes an image of the stable power. -/
@[simp]
theorem fittingRangeProjection_apply_pow (x : M) :
    fittingRangeProjection f n hK hI ((f ^ n) x) = (f ^ n) x :=
  fittingRangeProjection_apply_of_mem_range f n hK hI ⟨x, rfl⟩

/-- The kernel projection has the expected range and kernel. -/
theorem fittingKernelProjection_range_ker :
    LinearMap.range (fittingKernelProjection f n hK hI) = LinearMap.ker (f ^ n) ∧
      LinearMap.ker (fittingKernelProjection f n hK hI) = LinearMap.range (f ^ n) := by
  constructor
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact fittingKernelProjection_mem f n hK hI y
    · intro hx
      exact ⟨x, fittingKernelProjection_apply_of_mem_ker f n hK hI hx⟩
  · ext x
    constructor
    · intro hx
      have hs := fittingProjections_add_apply f n hK hI x
      rw [LinearMap.mem_ker.mp hx, zero_add] at hs
      exact hs ▸ fittingRangeProjection_mem f n hK hI x
    · intro hx
      exact LinearMap.mem_ker.mpr
        (fittingKernelProjection_apply_of_mem_range f n hK hI hx)

/-- The range projection has the expected range and kernel. -/
theorem fittingRangeProjection_range_ker :
    LinearMap.range (fittingRangeProjection f n hK hI) = LinearMap.range (f ^ n) ∧
      LinearMap.ker (fittingRangeProjection f n hK hI) = LinearMap.ker (f ^ n) := by
  constructor
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact fittingRangeProjection_mem f n hK hI y
    · intro hx
      exact ⟨x, fittingRangeProjection_apply_of_mem_range f n hK hI hx⟩
  · ext x
    constructor
    · intro hx
      have hs := fittingProjections_add_apply f n hK hI x
      rw [LinearMap.mem_ker.mp hx, add_zero] at hs
      exact hs ▸ fittingKernelProjection_mem f n hK hI x
    · intro hx
      exact LinearMap.mem_ker.mpr
        (fittingRangeProjection_apply_of_mem_ker f n hK hI hx)

/-- The two projections sum to the identity and are orthogonal idempotents. -/
theorem fittingProjections_identities :
    fittingKernelProjection f n hK hI + fittingRangeProjection f n hK hI = 1 ∧
      fittingKernelProjection f n hK hI ^ 2 = fittingKernelProjection f n hK hI ∧
      fittingRangeProjection f n hK hI ^ 2 = fittingRangeProjection f n hK hI ∧
      fittingKernelProjection f n hK hI * fittingRangeProjection f n hK hI = 0 ∧
      fittingRangeProjection f n hK hI * fittingKernelProjection f n hK hI = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    exact fittingProjections_add_apply f n hK hI x
  · ext x
    simpa only [pow_two, Module.End.mul_apply] using
      fittingKernelProjection_apply_of_mem_ker f n hK hI
        (fittingKernelProjection_mem f n hK hI x)
  · ext x
    simpa only [pow_two, Module.End.mul_apply] using
      fittingRangeProjection_apply_of_mem_range f n hK hI
        (fittingRangeProjection_mem f n hK hI x)
  · ext x
    exact fittingKernelProjection_apply_of_mem_range f n hK hI
      (fittingRangeProjection_mem f n hK hI x)
  · ext x
    exact fittingRangeProjection_apply_of_mem_ker f n hK hI
      (fittingKernelProjection_mem f n hK hI x)

/-- Each stable projection commutes with the endomorphism. -/
theorem fittingProjections_commute :
    fittingKernelProjection f n hK hI * f = f * fittingKernelProjection f n hK hI ∧
      fittingRangeProjection f n hK hI * f = f * fittingRangeProjection f n hK hI := by
  constructor
  · ext x
    obtain ⟨⟨k, i⟩, rfl⟩ := (fittingEquiv f n hK hI).surjective x
    change fittingKernelProjection f n hK hI (f ((k : M) + (i : M))) =
      f (fittingKernelProjection f n hK hI ((k : M) + (i : M)))
    rw [map_add, (fittingProjections_apply_add f n hK hI k i).1]
    exact (fittingProjections_apply_add f n hK hI
      (kerPowRestrict f n k) (rangePowRestrict f n i)).1
  · ext x
    obtain ⟨⟨k, i⟩, rfl⟩ := (fittingEquiv f n hK hI).surjective x
    change fittingRangeProjection f n hK hI (f ((k : M) + (i : M))) =
      f (fittingRangeProjection f n hK hI ((k : M) + (i : M)))
    rw [map_add, (fittingProjections_apply_add f n hK hI k i).2]
    exact (fittingProjections_apply_add f n hK hI
      (kerPowRestrict f n k) (rangePowRestrict f n i)).2

/-- The endomorphism has nilpotent and invertible diagonal blocks.
This is the block form of the Fitting decomposition (Wisbauer,
*Foundations of Module and Ring Theory*, §31.13), with semiring scalars,
additive-group carriers and explicit one-step stability in place of the cited
ring-module chain conditions. -/
theorem fittingEquiv_block :
    ((fittingEquiv f n hK hI).symm.toLinearMap.comp f).comp
        (fittingEquiv f n hK hI).toLinearMap =
      (kerPowRestrict f n).prodMap (fittingRangeAut f n hK hI).toLinearMap := by
  apply LinearMap.ext
  intro x
  change (fittingEquiv f n hK hI).symm (f (fittingEquiv f n hK hI x)) =
    (kerPowRestrict f n x.1, fittingRangeAut f n hK hI x.2)
  apply (fittingEquiv f n hK hI).symm_apply_eq.mpr
  simp only [fittingEquiv_apply, map_add, kerPowRestrict_apply, fittingRangeAut_apply]

/-- At bound zero, the one-step hypotheses force the endomorphism to be bijective. -/
theorem bijective_of_stable_zero
    (hK0 : LinearMap.ker (f ^ 0) = LinearMap.ker (f ^ (0 + 1)))
    (hI0 : LinearMap.range (f ^ 0) = LinearMap.range (f ^ (0 + 1))) :
    Function.Bijective f := by
  constructor
  · apply (LinearMap.ker_eq_bot_of_semiring f).mp
    simpa only [pow_zero, pow_one, zero_add, Module.End.one_eq_id,
      LinearMap.ker_id] using hK0.symm
  · apply LinearMap.range_eq_top.mp
    simpa only [pow_zero, pow_one, zero_add, Module.End.one_eq_id,
      LinearMap.range_id] using hI0.symm

/-- At bound zero the kernel projection vanishes and the range projection is the identity. -/
theorem fittingProjections_zero_bound
    (hK0 : LinearMap.ker (f ^ 0) = LinearMap.ker (f ^ (0 + 1)))
    (hI0 : LinearMap.range (f ^ 0) = LinearMap.range (f ^ (0 + 1))) :
    fittingKernelProjection f 0 hK0 hI0 = 0 ∧ fittingRangeProjection f 0 hK0 hI0 = 1 := by
  have hp : fittingKernelProjection f 0 hK0 hI0 = 0 := by
    ext x
    have hx := LinearMap.mem_ker.mp (fittingKernelProjection_mem f 0 hK0 hI0 x)
    simpa only [pow_zero, Module.End.one_apply, LinearMap.zero_apply] using hx
  refine ⟨hp, ?_⟩
  have hs := (fittingProjections_identities f 0 hK0 hI0).1
  simpa only [hp, zero_add] using hs

/-- Stable ambient projections are independent of the stable bound. -/
theorem fittingProjections_eq_of_stable (m : ℕ)
    (hKm : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (m + 1)))
    (hIm : LinearMap.range (f ^ m) = LinearMap.range (f ^ (m + 1))) :
    fittingKernelProjection f n hK hI = fittingKernelProjection f m hKm hIm ∧
      fittingRangeProjection f n hK hI = fittingRangeProjection f m hKm hIm := by
  obtain ⟨hKeq, hIeq⟩ := stable_submodules_eq f n hK hI m hKm hIm
  have hRange : fittingRangeProjection f n hK hI = fittingRangeProjection f m hKm hIm := by
    apply LinearMap.ext
    intro x
    apply (fittingRangeProjection_unique f m hKm hIm x _).mpr
    constructor
    · rw [← hIeq]
      exact fittingRangeProjection_mem f n hK hI x
    · have hk_mem : fittingKernelProjection f n hK hI x ∈ LinearMap.ker (f ^ m) := by
        rw [← hKeq]
        exact fittingKernelProjection_mem f n hK hI x
      have hk := LinearMap.mem_ker.mp hk_mem
      have hpower := congrArg (f ^ m) (fittingProjections_add_apply f n hK hI x)
      simpa only [map_add, hk, zero_add] using hpower
  refine ⟨?_, hRange⟩
  apply LinearMap.ext
  intro x
  calc
    fittingKernelProjection f n hK hI x = x - fittingRangeProjection f n hK hI x :=
      fittingKernelProjection_apply f n hK hI x
    _ = x - fittingRangeProjection f m hKm hIm x :=
      congrArg (fun y : M => x - y) (LinearMap.congr_fun hRange x)
    _ = fittingKernelProjection f m hKm hIm x :=
      (fittingKernelProjection_apply f m hKm hIm x).symm

/-- Inverse components at different stable bounds agree in the ambient module. -/
theorem fittingEquiv_symm_coe_eq_of_stable (m : ℕ)
    (hKm : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (m + 1)))
    (hIm : LinearMap.range (f ^ m) = LinearMap.range (f ^ (m + 1))) (x : M) :
    (((fittingEquiv f n hK hI).symm x).1 : M) =
        (((fittingEquiv f m hKm hIm).symm x).1 : M) ∧
      (((fittingEquiv f n hK hI).symm x).2 : M) =
        (((fittingEquiv f m hKm hIm).symm x).2 : M) := by
  obtain ⟨hKernel, hRange⟩ := fittingProjections_eq_of_stable f n hK hI m hKm hIm
  exact ⟨(fittingEquiv_symm_apply_coe f n hK hI x).1.trans
      ((LinearMap.congr_fun hKernel x).trans (fittingEquiv_symm_apply_coe f m hKm hIm x).1.symm),
    (fittingEquiv_symm_apply_coe f n hK hI x).2.trans
      ((LinearMap.congr_fun hRange x).trans (fittingEquiv_symm_apply_coe f m hKm hIm x).2.symm)⟩

section Naturality

variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {P : Type uP} [AddCommGroup P] [Module R P]

/-- The invertible components' inverse maps also intertwine. -/
theorem fittingRangeAut_symm_natural (g : Module.End R N) (m : ℕ)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (hIg : LinearMap.range (g ^ m) = LinearMap.range (g ^ (m + 1)))
    (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) :
    (rangePowIntertwiner f n hI g m h hh).comp
        (fittingRangeAut f n hK hI).symm.toLinearMap =
      (fittingRangeAut g m hKg hIg).symm.toLinearMap.comp
        (rangePowIntertwiner f n hI g m h hh) := by
  let a := fittingRangeAut f n hK hI
  let b := fittingRangeAut g m hKg hIg
  let t := rangePowIntertwiner f n hI g m h hh
  have ht : t.comp a.toLinearMap = b.toLinearMap.comp t :=
    (fittingRestrictions_natural f n hI g m hKg h hh).2
  apply LinearMap.ext
  intro x
  apply b.injective
  change b (t (a.symm x)) = b (b.symm (t x))
  calc
    b (t (a.symm x)) = t (a (a.symm x)) :=
      (LinearMap.congr_fun ht (a.symm x)).symm
    _ = t x := congrArg t (a.apply_symm_apply x)
    _ = b (b.symm (t x)) := (b.apply_symm_apply (t x)).symm

/-- Arbitrary linear intertwiners commute with both stable projections. -/
theorem fittingProjections_natural (g : Module.End R N) (m : ℕ)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (hIg : LinearMap.range (g ^ m) = LinearMap.range (g ^ (m + 1)))
    (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) :
    h.comp (fittingKernelProjection f n hK hI) =
        (fittingKernelProjection g m hKg hIg).comp h ∧
      h.comp (fittingRangeProjection f n hK hI) =
        (fittingRangeProjection g m hKg hIg).comp h := by
  have hparts (x : M) :
      h (fittingKernelProjection f n hK hI x) = fittingKernelProjection g m hKg hIg (h x) ∧
        h (fittingRangeProjection f n hK hI x) = fittingRangeProjection g m hKg hIg (h x) := by
    let p := (fittingEquiv f n hK hI).symm x
    have hx : (p.1 : M) + (p.2 : M) = x :=
      (fittingEquiv f n hK hI).apply_symm_apply x
    have hp := fittingProjections_apply_add g m hKg hIg
      (kerPowIntertwiner f n g m h hh hKg p.1)
      (rangePowIntertwiner f n hI g m h hh p.2)
    have hsum : (kerPowIntertwiner f n g m h hh hKg p.1 : N) +
        (rangePowIntertwiner f n hI g m h hh p.2 : N) = h x :=
      (h.map_add (p.1 : M) (p.2 : M)).symm.trans (congrArg h hx)
    rw [hsum] at hp
    exact ⟨hp.1.symm, hp.2.symm⟩
  constructor
  · apply LinearMap.ext
    intro x
    exact (hparts x).1
  · apply LinearMap.ext
    intro x
    exact (hparts x).2

/-- The stable sum equivalences are natural for arbitrary linear intertwiners. -/
theorem fittingEquiv_natural (g : Module.End R N) (m : ℕ)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (hIg : LinearMap.range (g ^ m) = LinearMap.range (g ^ (m + 1)))
    (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) :
    h.comp (fittingEquiv f n hK hI).toLinearMap =
      (fittingEquiv g m hKg hIg).toLinearMap.comp
        ((kerPowIntertwiner f n g m h hh hKg).prodMap
          (rangePowIntertwiner f n hI g m h hh)) := by
  apply LinearMap.ext
  intro x
  change h ((x.1 : M) + (x.2 : M)) = h (x.1 : M) + h (x.2 : M)
  exact h.map_add _ _

/-- The inverse-coordinate naturality square for an arbitrary linear intertwiner. -/
theorem fittingEquiv_symm_natural (g : Module.End R N) (m : ℕ)
    (hKg : LinearMap.ker (g ^ m) = LinearMap.ker (g ^ (m + 1)))
    (hIg : LinearMap.range (g ^ m) = LinearMap.range (g ^ (m + 1)))
    (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) :
    ((kerPowIntertwiner f n g m h hh hKg).prodMap
        (rangePowIntertwiner f n hI g m h hh)).comp
        (fittingEquiv f n hK hI).symm.toLinearMap =
      (fittingEquiv g m hKg hIg).symm.toLinearMap.comp h := by
  let a := fittingEquiv f n hK hI
  let b := fittingEquiv g m hKg hIg
  let t := (kerPowIntertwiner f n g m h hh hKg).prodMap
    (rangePowIntertwiner f n hI g m h hh)
  have ht : h.comp a.toLinearMap = b.toLinearMap.comp t :=
    fittingEquiv_natural f n hK hI g m hKg hIg h hh
  apply LinearMap.ext
  intro x
  apply b.injective
  change b (t (a.symm x)) = b (b.symm (h x))
  calc
    b (t (a.symm x)) = h (a (a.symm x)) :=
      (LinearMap.congr_fun ht (a.symm x)).symm
    _ = h x := congrArg h (a.apply_symm_apply x)
    _ = b (b.symm (h x)) := (b.apply_symm_apply (h x)).symm

end Naturality

end AddCommGroup

section RingBridge

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- Agreement with the stock ring-scalar complement sum equivalence. -/
theorem fittingEquiv_eq_prodEquivOfIsCompl (f : Module.End R M) (n : ℕ)
    (hK : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hI : LinearMap.range (f ^ n) = LinearMap.range (f ^ (n + 1)))
    (h : IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n))) :
    fittingEquiv f n hK hI =
      Submodule.prodEquivOfIsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) h := by
  ext x
  rfl

end RingBridge

end Module.End

namespace IsNoetherian

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module R M] [IsNoetherian R M]

/-- A surjective endomorphism of a Noetherian additive-group module is injective. -/
theorem injective_of_surjective_endomorphism_of_semiring (f : Module.End R M)
    (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  apply (LinearMap.ker_eq_bot_of_semiring f).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := Module.End.iterate_surjective hf n x
  have hy : y ∈ LinearMap.ker (f ^ (n + 1)) := by
    change (f ^ (n + 1)) y = 0
    rw [pow_succ', Module.End.mul_apply]
    exact hx
  rw [← hn _ (Nat.le_succ n)] at hy
  exact hy

/-- A surjective endomorphism of a Noetherian additive-group module is bijective. -/
theorem bijective_of_surjective_endomorphism_of_semiring (f : Module.End R M)
    (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨injective_of_surjective_endomorphism_of_semiring f hf, hf⟩

end IsNoetherian

namespace Module.End

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module R M] [IsNoetherian R M]

/-- The automorphism induced by a surjective endomorphism of a Noetherian module. -/
noncomputable def equivOfSurjectiveOfIsNoetherian (f : Module.End R M)
    (hf : Function.Surjective f) : M ≃ₗ[R] M :=
  { f with
    invFun := @Function.invFun M M ⟨0⟩ f
    left_inv := Function.leftInverse_invFun
      (IsNoetherian.injective_of_surjective_endomorphism_of_semiring f hf)
    right_inv := Function.rightInverse_invFun hf }

@[simp]
theorem equivOfSurjectiveOfIsNoetherian_apply (f : Module.End R M)
    (hf : Function.Surjective f) (x : M) :
    equivOfSurjectiveOfIsNoetherian f hf x = f x := rfl

@[simp]
theorem equivOfSurjectiveOfIsNoetherian_symm_apply (f : Module.End R M)
    (hf : Function.Surjective f) (x : M) :
    (equivOfSurjectiveOfIsNoetherian f hf).symm x =
      @Function.invFun M M ⟨0⟩ f x := rfl

end Module.End

namespace Module.End

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M] [IsNoetherian R M]

/-- Over a ring, the semiring construction agrees with the bijective-endomorphism equivalence. -/
theorem equivOfSurjectiveOfIsNoetherian_eq_ofBijective (f : Module.End R M)
    (hf : Function.Surjective f) :
    equivOfSurjectiveOfIsNoetherian f hf =
      LinearEquiv.ofBijective f (IsNoetherian.bijective_of_surjective_endomorphism f hf) := by
  ext x
  rfl

end Module.End
