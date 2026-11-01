/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicCofinalityMul
public import CoherentModules.RingTheory.Ideal.AdicCofinalitySup

public import CoherentModules.Algebra.Module.LocalizedModule
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Submodule adic cofinality

`Ideal.HasSubmoduleAdicCofinality` says that the intrinsic ideal-power filtration
of every submodule of a finite module is cofinal with the filtration induced from
the ambient module. `Ideal.HasFiniteSubmoduleAdicCofinality` restricts this
condition to finitely generated submodules. These are Fujiwara--Kato's conditions
(AP) and (APf), respectively; neither asks for the shifted equality of Artin–Rees.
Neither the ideal nor the relations of the ambient module need be finitely generated.

Full submodule adic cofinality implies finite-submodule adic cofinality.
Both conditions are invariant under equivalences of coefficient rings and under
mutually cofinal ideal powers, and hence under replacing an ideal by any positive
power. They also pass to the extension of an ideal along a module-finite algebra
or an arbitrary localization algebra.
Nilpotent ideals satisfy both conditions without any Noetherian hypothesis. The
Noetherian-ring providers are in `CoherentModules.RingTheory.Filtration`.

The pointwise comparisons `Submodule.adic_cofinality_iff_of_pow_le` and
`Submodule.adic_cofinality_iff_of_semilinearEquiv` apply to arbitrary left ideals
of a semiring and arbitrary submodules of a semimodule, without any finiteness or
additive-inverse assumption. Semilinear transport maps both the ideal and the
submodule, using the original scalar actions, and preserves each pair of
filtration indices.

## Implementation notes

The predicates quantify over modules in the ring's universe. Their `.cofinal`
eliminators apply in any module universe, using Mathlib's `Module.Finite.reprEquiv`
and identity-coefficient specialization of the semilinear transport of the whole
inequality. The representative is a quotient of a finite free module by its full
kernel; no finite-presentation assumption is made.

Semilinear transport uses Mathlib's submodule map and order-reflection APIs.
The ideal-power action commutes with the image of any semilinear map whose
coefficient homomorphism is surjective; the module map need not be bijective.
Its identity-coefficient, exponent-one specialization is Mathlib's
`Submodule.map_smul''`. The power induction uses associativity of the ideal
action, without a right-unit law for arbitrary left ideals.

Power comparison uses Mathlib's monotonicity of left-ideal powers and ideal
actions. For arbitrary left ideals, the power-addition formula needs a nonzero
right exponent; rescaling by zero is handled separately with powers of the unit
ideal. Both power-comparison witnesses may be zero.

Finite-algebra transport uses the action composed with the algebra map.
Restriction of scalars preserves intersections and mapped ideal-power actions.
Finiteness is transitive, and finite generation of a submodule also restricts
along a module-finite algebra.

For localization transport, a finite target module is the localization of a
finitely generated submodule over the original ring; it need not itself be
finite over that ring. Full cofinality uses the whole preimage of the target
submodule. Finite-submodule cofinality instead uses a finitely generated
representative supplied by `Submodule.FG.exists_localized'_eq`; the whole
preimage need not be finitely generated. Both proofs localize the same kind of
stage inclusion using the localized-submodule intersection and ideal-action APIs.
The given target algebra action is unchanged.

## References

Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
arXiv:1308.4734v5 (2017-02-28), §0.7.4, the (AP)/(APf) paragraph on printed
page 167, and Exercise 0.7.8 on printed page 173.
The universe bridges and semilinear transport use Mathlib's finite-module
representatives and submodule map, order-reflection, finite-generation and
ideal-action APIs. The filtered-action image identity extends Mathlib's
`Submodule.map_smul''` to semilinear maps with surjective coefficient homomorphisms.
-/

@[expose] public section

universe uR uS uA uM uP

namespace Submodule

private theorem map_ideal_smul
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {M : Type uM} {P : Type uP}
    [AddCommMonoid M] [AddCommMonoid P] [Module R M] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ]
    (f : M →ₛₗ[σ] P) (I : Ideal R) (N : Submodule R M) :
    (I • N).map f = (I.map σ) • N.map f := by
  refine le_antisymm ?_ ?_
  · refine Submodule.map_le_iff_le_comap.mpr ?_
    refine Submodule.smul_le.mpr ?_
    intro r hr n hn
    apply Submodule.mem_comap.mpr
    rw [map_smulₛₗ f]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem σ hr)
      (Submodule.mem_map_of_mem hn)
  · refine Submodule.smul_le.mpr ?_
    intro s hs p hp
    obtain ⟨r, hr, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective σ σ.surjective).mp hs
    obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.mp hp
    rw [← map_smulₛₗ f]
    exact Submodule.mem_map_of_mem (Submodule.smul_mem_smul hr hn)

private theorem map_ideal_pow_smul
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {M : Type uM} {P : Type uP}
    [AddCommMonoid M] [AddCommMonoid P] [Module R M] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ]
    (f : M →ₛₗ[σ] P) (I : Ideal R) (N : Submodule R M) (k : ℕ) :
    ((I ^ k) • N).map f = ((I.map σ) ^ k) • N.map f := by
  induction k generalizing N with
  | zero =>
    simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  | succ k ih =>
    rw [Submodule.pow_succ, Submodule.mul_smul, ih, map_ideal_smul,
      Submodule.pow_succ, Submodule.mul_smul]

private theorem map_ideal_pow_smul_one_id
    {R : Type uR} [Semiring R]
    {M : Type uM} {P : Type uP}
    [AddCommMonoid M] [AddCommMonoid P] [Module R M] [Module R P]
    (f : M →ₗ[R] P) (I : Ideal R) (N : Submodule R M) :
    ((I ^ 1) • N).map f =
      ((I.map (RingHom.id R)) ^ 1) • N.map f := by
  simpa only [Submodule.pow_one, Ideal.map_id] using (Submodule.map_smul'' I N f)

private theorem ideal_pow_mul {R : Type uR} [Semiring R]
    (I : Ideal R) (a n : ℕ) : I ^ (a * n) = (I ^ a) ^ n := by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [Nat.zero_mul, Submodule.pow_zero, Ideal.one_eq_top, Ideal.top_pow]
  · induction n with
    | zero => simp only [Nat.mul_zero, Submodule.pow_zero]
    | succ n ih =>
      rw [Nat.mul_succ, Submodule.pow_add I ha, Submodule.pow_succ, ih]

private theorem adic_cofinality_of_pow_le
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (N : Submodule R M) {I J : Ideal R}
    {a b : ℕ} (hIJ : I ^ a ≤ J) (hJI : J ^ b ≤ I)
    (hI : ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((J ^ m) • (⊤ : Submodule R M)) ≤ (J ^ n) • N := by
  intro n
  obtain ⟨k, hk⟩ := hI (a * n)
  refine ⟨b * k, ?_⟩
  have hJk : J ^ (b * k) ≤ I ^ k := by
    rw [ideal_pow_mul]
    exact Ideal.pow_right_mono hJI k
  have hIn : I ^ (a * n) ≤ J ^ n := by
    rw [ideal_pow_mul]
    exact Ideal.pow_right_mono hIJ n
  calc
    N ⊓ ((J ^ (b * k)) • (⊤ : Submodule R M))
        ≤ N ⊓ ((I ^ k) • (⊤ : Submodule R M)) :=
      inf_le_inf_left N (Submodule.smul_mono_left hJk)
    _ ≤ (I ^ (a * n)) • N := hk
    _ ≤ (J ^ n) • N := Submodule.smul_mono_left hIn

/-- Mutually cofinal powers of left ideals give equivalent cofinality conditions
for the intrinsic and induced filtrations on a submodule. The ambient module
and submodule need not be finite, and the power-comparison witnesses may be zero.
This uses the given scalar action and allows independent ring and module universes. -/
theorem adic_cofinality_iff_of_pow_le
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (N : Submodule R M) {I J : Ideal R}
    (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    (∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N) ↔
    (∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((J ^ m) • (⊤ : Submodule R M)) ≤ (J ^ n) • N) := by
  obtain ⟨a, ha⟩ := hIJ
  obtain ⟨b, hb⟩ := hJI
  exact ⟨adic_cofinality_of_pow_le N ha hb, adic_cofinality_of_pow_le N hb ha⟩

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Submodule adic cofinality is invariant under a semilinear equivalence over
an equivalence of coefficient semirings, for the two given scalar actions. -/
theorem adic_cofinality_iff_of_semilinearEquiv
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {M : Type uM} {P : Type uP}
    [AddCommMonoid M] [AddCommMonoid P] [Module R M] [Module S P]
    (σ : R ≃+* S) (e : M ≃ₛₗ[(σ : R →+* S)] P)
    (I : Ideal R) (N : Submodule R M) :
    (∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N) ↔
    (∀ n : ℕ, ∃ m : ℕ,
      N.map e.toLinearMap ⊓
          (((I.map σ.toRingHom) ^ m) • (⊤ : Submodule S P)) ≤
        ((I.map σ.toRingHom) ^ n) • N.map e.toLinearMap) := by
  refine forall_congr' fun n => exists_congr fun m => ?_
  simpa only [RingEquiv.toRingHom_eq_coe,
    Submodule.map_inf _ e.injective, map_ideal_pow_smul,
    Submodule.map_top,
    LinearMap.range_eq_top_of_surjective e.toLinearMap e.surjective] using
    (Submodule.map_le_map_iff_of_injective (f := e.toLinearMap) e.injective
      (N ⊓ ((I ^ m) • (⊤ : Submodule R M))) ((I ^ n) • N)).symm

/-- Vanishing of an induced-filtration stage on every nilpotent quotient image
of a submodule implies adic cofinality for that submodule. -/
private theorem adic_cofinality_of_quotient_image
    {R : Type uR} [Ring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : Submodule R M)
    (h : ∀ (Q : Submodule R M),
      (∃ k : ℕ, (I ^ k) • (N.map Q.mkQ) = ⊥) →
        ∃ m : ℕ, N.map Q.mkQ ⊓
          ((I ^ m) • (⊤ : Submodule R (M ⧸ Q))) = ⊥) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  intro n
  let Q : Submodule R M := (I ^ n) • N
  have hkill : (I ^ n) • N.map Q.mkQ = ⊥ := by
    rw [← Submodule.map_smul'']
    exact Q.mkQ_map_self
  obtain ⟨m, hm⟩ := h Q ⟨n, hkill⟩
  refine ⟨m, ?_⟩
  calc
    N ⊓ ((I ^ m) • (⊤ : Submodule R M))
        ≤ (N.map Q.mkQ ⊓
          ((I ^ m) • (⊤ : Submodule R (M ⧸ Q)))).comap Q.mkQ := by
      rw [Submodule.comap_inf]
      exact inf_le_inf (Submodule.le_comap_map Q.mkQ N)
        (Submodule.smul_top_le_comap_smul_top (I ^ m) Q.mkQ)
    _ = Q := by rw [hm, Submodule.comap_bot, Submodule.ker_mkQ]
    _ = (I ^ n) • N := rfl

end Submodule

namespace Ideal

variable {R : Type uR} [CommRing R]

/-- The intrinsic and induced ideal-power filtrations are cofinal on every
submodule of every finite module. This is condition (AP) of Fujiwara--Kato,
*Foundations of Rigid Geometry I*, §0.7.4.

Use `HasSubmoduleAdicCofinality.cofinal` for modules in an arbitrary universe.
Neither the ideal nor the submodule need be finitely generated, and the ambient
module need not be finitely presented. -/
def HasSubmoduleAdicCofinality (I : Ideal R) : Prop :=
  ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
    (K : Submodule R X),
    ∀ n : ℕ, ∃ m : ℕ,
      K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K

/-- The defining cofinality condition, also providing the constructor for
`HasSubmoduleAdicCofinality`. For elimination in an independent module universe,
use `HasSubmoduleAdicCofinality.cofinal`. -/
theorem hasSubmoduleAdicCofinality_iff (I : Ideal R) :
    I.HasSubmoduleAdicCofinality ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (K : Submodule R X),
        ∀ n : ℕ, ∃ m : ℕ,
          K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K :=
  Iff.rfl

private theorem cofinal_of_linearEquiv
    (I : Ideal R) {X : Type*} [AddCommGroup X] [Module R X]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (e : X ≃ₗ[R] M) (N : Submodule R M)
    (hN : ∀ n : ℕ, ∃ m : ℕ,
      N.map e.symm.toLinearMap ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤
        (I ^ n) • N.map e.symm.toLinearMap) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  have hmap : (N.map e.symm.toLinearMap).map e.toLinearMap = N :=
    (Submodule.map_symm_eq_iff e).mp rfl
  have h := (Submodule.adic_cofinality_iff_of_semilinearEquiv
    (R := R) (S := R) (M := X) (P := M) (RingEquiv.refl R) e I
    (N.map e.symm.toLinearMap)).mp hN
  simp only [RingEquiv.toRingHom_refl, Ideal.map_id] at h
  change ∀ n : ℕ, ∃ m : ℕ,
    (N.map e.symm.toLinearMap).map e.toLinearMap ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤
      (I ^ n) • (N.map e.symm.toLinearMap).map e.toLinearMap at h
  simpa only [hmap] using h

/-- Submodule adic cofinality applies to the given module and scalar action in
any module universe, independently of the ring universe. No finite generation
of the submodule is required. -/
theorem HasSubmoduleAdicCofinality.cofinal
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  let e := Module.Finite.reprEquiv R M
  exact cofinal_of_linearEquiv I e N
    ((hasSubmoduleAdicCofinality_iff I).mp hI
      (Module.Finite.repr R M) (N.map e.symm.toLinearMap))

/-- The intrinsic and induced ideal-power filtrations are cofinal on every
finitely generated submodule of every finite module. This is condition (APf)
of Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4.

Use `HasFiniteSubmoduleAdicCofinality.cofinal` for modules in an arbitrary
universe. The ideal need not be finitely generated, and the ambient module
need not be finitely presented. -/
def HasFiniteSubmoduleAdicCofinality (I : Ideal R) : Prop :=
  ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
    (K : Submodule R X), K.FG →
    ∀ n : ℕ, ∃ m : ℕ,
      K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K

/-- The defining cofinality condition, also providing the constructor for
`HasFiniteSubmoduleAdicCofinality`. For elimination in an independent module
universe, use `HasFiniteSubmoduleAdicCofinality.cofinal`. -/
theorem hasFiniteSubmoduleAdicCofinality_iff (I : Ideal R) :
    I.HasFiniteSubmoduleAdicCofinality ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (K : Submodule R X), K.FG →
        ∀ n : ℕ, ∃ m : ℕ,
          K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K :=
  Iff.rfl

/-- Condition (AP) implies condition (APf) by restricting to finitely generated
submodules. -/
theorem HasSubmoduleAdicCofinality.hasFiniteSubmoduleAdicCofinality
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality) :
    I.HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro X _ _ _ K _
  exact hI.cofinal K

/-- Finite-submodule adic cofinality applies to the given module and scalar
action in any module universe, independently of the ring universe. -/
theorem HasFiniteSubmoduleAdicCofinality.cofinal
    {I : Ideal R} (hI : I.HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (hN : N.FG) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  let e := Module.Finite.reprEquiv R M
  exact cofinal_of_linearEquiv I e N
    ((hasFiniteSubmoduleAdicCofinality_iff I).mp hI
      (Module.Finite.repr R M) (N.map e.symm.toLinearMap) (hN.map e.symm.toLinearMap))

/-- In a finite ambient module, condition (AP) gives a zero induced-filtration
stage on any submodule killed by one common ideal power. Neither the ideal nor
the submodule need be finitely generated. The module universe is independent of
the ring universe, and the given scalar action is unchanged.

This is the forward implication of Fujiwara--Kato, *Foundations of Rigid
Geometry I*, Exercise 0.7.8. -/
theorem HasSubmoduleAdicCofinality.exists_inf_pow_smul_eq_bot
    {R : Type uR} [CommRing R] {I : Ideal R}
    (hI : I.HasSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (hkill : ∃ n : ℕ, (I ^ n) • N = ⊥) :
    ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R M)) = ⊥ := by
  obtain ⟨k, hk⟩ := hkill
  obtain ⟨m, hm⟩ := hI.cofinal N k
  refine ⟨m, le_antisymm ?_ bot_le⟩
  simpa only [hk] using hm

/-- In a finite ambient module, condition (APf) gives a zero induced-filtration
stage on a finitely generated submodule killed by one common ideal power. The
ideal need not be finitely generated. The module universe is independent of
the ring universe, and the given scalar action is unchanged.

This is the forward implication of Fujiwara--Kato, *Foundations of Rigid
Geometry I*, Exercise 0.7.8. -/
theorem HasFiniteSubmoduleAdicCofinality.exists_inf_pow_smul_eq_bot
    {R : Type uR} [CommRing R] {I : Ideal R}
    (hI : I.HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (hN : N.FG)
    (hkill : ∃ n : ℕ, (I ^ n) • N = ⊥) :
    ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R M)) = ⊥ := by
  obtain ⟨k, hk⟩ := hkill
  obtain ⟨m, hm⟩ := hI.cofinal N hN k
  refine ⟨m, le_antisymm ?_ bot_le⟩
  simpa only [hk] using hm

/-- Condition (AP) is equivalent to existence of a zero induced-filtration stage
for every submodule killed by one common ideal power in a finite ambient module.
Neither the ideal nor the tested submodule need be finitely generated.

This is Fujiwara--Kato, *Foundations of Rigid Geometry I*, Exercise 0.7.8. -/
theorem hasSubmoduleAdicCofinality_iff_forall_exists_inf_pow_smul_eq_bot
    {R : Type uR} [CommRing R] (I : Ideal R) :
    I.HasSubmoduleAdicCofinality ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (N : Submodule R X),
        (∃ n : ℕ, (I ^ n) • N = ⊥) →
          ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R X)) = ⊥ := by
  constructor
  · intro hI X _ _ _ N hkill
    exact hI.exists_inf_pow_smul_eq_bot N hkill
  · intro h
    refine (hasSubmoduleAdicCofinality_iff I).2 ?_
    intro X _ _ _ N
    refine Submodule.adic_cofinality_of_quotient_image I N ?_
    intro Q hkill
    let : Module.Finite R (X ⧸ Q) := Module.Finite.quotient R Q
    exact h (X ⧸ Q) (N.map Q.mkQ) hkill

/-- Condition (APf) is equivalent to existence of a zero induced-filtration stage
for every finitely generated submodule killed by one common ideal power in a
finite ambient module. The ideal need not be finitely generated, and the ambient
module need not be finitely presented.

This is Fujiwara--Kato, *Foundations of Rigid Geometry I*, Exercise 0.7.8. -/
theorem hasFiniteSubmoduleAdicCofinality_iff_forall_exists_inf_pow_smul_eq_bot
    {R : Type uR} [CommRing R] (I : Ideal R) :
    I.HasFiniteSubmoduleAdicCofinality ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (N : Submodule R X), N.FG →
        (∃ n : ℕ, (I ^ n) • N = ⊥) →
          ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R X)) = ⊥ := by
  constructor
  · intro hI X _ _ _ N hN hkill
    exact hI.exists_inf_pow_smul_eq_bot N hN hkill
  · intro h
    refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
    intro X _ _ _ N hN
    refine Submodule.adic_cofinality_of_quotient_image I N ?_
    intro Q hkill
    let : Module.Finite R (X ⧸ Q) := Module.Finite.quotient R Q
    exact h (X ⧸ Q) (N.map Q.mkQ) (hN.map Q.mkQ) hkill

/-- Submodule adic cofinality is invariant under mutual containment of ideal powers. -/
theorem hasSubmoduleAdicCofinality_iff_of_pow_le
    {R : Type uR} [CommRing R] {I J : Ideal R}
    (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    I.HasSubmoduleAdicCofinality ↔ J.HasSubmoduleAdicCofinality := by
  constructor
  · intro hI
    refine (Ideal.hasSubmoduleAdicCofinality_iff J).mpr ?_
    intro M _ _ _ N
    exact (Submodule.adic_cofinality_iff_of_pow_le N hIJ hJI).mp
      (hI.cofinal N)
  · intro hJ
    refine (Ideal.hasSubmoduleAdicCofinality_iff I).mpr ?_
    intro M _ _ _ N
    exact (Submodule.adic_cofinality_iff_of_pow_le N hIJ hJI).mpr
      (hJ.cofinal N)

/-- Finite-submodule adic cofinality is invariant under mutual containment of
ideal powers. -/
theorem hasFiniteSubmoduleAdicCofinality_iff_of_pow_le
    {R : Type uR} [CommRing R] {I J : Ideal R}
    (hIJ : ∃ a : ℕ, I ^ a ≤ J)
    (hJI : ∃ b : ℕ, J ^ b ≤ I) :
    I.HasFiniteSubmoduleAdicCofinality ↔ J.HasFiniteSubmoduleAdicCofinality := by
  constructor
  · intro hI
    refine (Ideal.hasFiniteSubmoduleAdicCofinality_iff J).mpr ?_
    intro M _ _ _ N hN
    exact (Submodule.adic_cofinality_iff_of_pow_le N hIJ hJI).mp
      (hI.cofinal N hN)
  · intro hJ
    refine (Ideal.hasFiniteSubmoduleAdicCofinality_iff I).mpr ?_
    intro M _ _ _ N hN
    exact (Submodule.adic_cofinality_iff_of_pow_le N hIJ hJI).mpr
      (hJ.cofinal N hN)

/-- An ideal and any of its positive powers have the same submodule adic
cofinality property. -/
theorem hasSubmoduleAdicCofinality_pow_iff
    {R : Type uR} [CommRing R]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    (I ^ n).HasSubmoduleAdicCofinality ↔ I.HasSubmoduleAdicCofinality := by
  exact Ideal.hasSubmoduleAdicCofinality_iff_of_pow_le (I := I ^ n) (J := I)
    ⟨1, by
      simpa only [pow_one] using
        (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hn))⟩
    ⟨n, le_rfl⟩

/-- An ideal and any of its positive powers have the same finite-submodule adic
cofinality property. -/
theorem hasFiniteSubmoduleAdicCofinality_pow_iff
    {R : Type uR} [CommRing R]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    (I ^ n).HasFiniteSubmoduleAdicCofinality ↔
      I.HasFiniteSubmoduleAdicCofinality := by
  exact Ideal.hasFiniteSubmoduleAdicCofinality_iff_of_pow_le (I := I ^ n) (J := I)
    ⟨1, by
      simpa only [pow_one] using
        (Ideal.pow_le_self (I := I) (Nat.ne_of_gt hn))⟩
    ⟨n, le_rfl⟩

private theorem cofinal_le_of_restrictScalars
    {S : Type uS} [CommRing S] [Algebra R S]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R) (N : Submodule S M) (m n : ℕ)
    (h : N.restrictScalars R ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤
      (I ^ n) • N.restrictScalars R) :
    N ⊓ (((I.map (algebraMap R S)) ^ m) • (⊤ : Submodule S M)) ≤
      ((I.map (algebraMap R S)) ^ n) • N := by
  apply (Submodule.restrictScalars_le R).mp
  simpa only [Submodule.restrictScalars_inf, ← Ideal.map_pow,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top] using h

/-- Submodule adic cofinality passes to the extension of an ideal along a
module-finite algebra. This is finite-algebra stability of condition (AP) of
Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4. Neither the ideal nor
the submodules need be finitely generated. -/
theorem HasSubmoduleAdicCofinality.map
    {S : Type uS} [CommRing S] [Algebra R S] [Module.Finite R S]
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality) :
    (I.map (algebraMap R S)).HasSubmoduleAdicCofinality := by
  refine (hasSubmoduleAdicCofinality_iff _).2 ?_
  intro X _ _ _ N n
  let : Module R X := Module.compHom X (algebraMap R S)
  let : IsScalarTower R S X := IsScalarTower.of_compHom R S X
  let : Module.Finite R X := Module.Finite.trans (R := R) S X
  obtain ⟨m, hm⟩ := hI.cofinal (N.restrictScalars R) n
  exact ⟨m, cofinal_le_of_restrictScalars I N m n hm⟩

/-- Finite-submodule adic cofinality passes to the extension of an ideal along a
module-finite algebra. This is finite-algebra stability of condition (APf) of
Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4. No finite generation
of the ideal is required. -/
theorem HasFiniteSubmoduleAdicCofinality.map
    {S : Type uS} [CommRing S] [Algebra R S] [Module.Finite R S]
    {I : Ideal R} (hI : I.HasFiniteSubmoduleAdicCofinality) :
    (I.map (algebraMap R S)).HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff _).2 ?_
  intro X _ _ _ N hN n
  let : Module R X := Module.compHom X (algebraMap R S)
  let : IsScalarTower R S X := IsScalarTower.of_compHom R S X
  let : Module.Finite R X := Module.Finite.trans (R := R) S X
  obtain ⟨m, hm⟩ := hI.cofinal (N.restrictScalars R) (hN.restrictScalars (R := R)) n
  exact ⟨m, cofinal_le_of_restrictScalars I N m n hm⟩

/-- Condition (AP) is invariant under an equivalence of coefficient rings. -/
theorem hasSubmoduleAdicCofinality_iff_of_ringEquiv
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (σ : R ≃+* S) (I : Ideal R) :
    I.HasSubmoduleAdicCofinality ↔
      (I.map σ.toRingHom).HasSubmoduleAdicCofinality := by
  constructor
  · intro hI
    let : Algebra R S := σ.toRingHom.toAlgebra
    let : Module.Finite R S := σ.finite
    simpa only [RingHom.algebraMap_toAlgebra] using
      (hI.map (S := S))
  · intro hI
    let : Algebra S R := σ.symm.toRingHom.toAlgebra
    let : Module.Finite S R := σ.symm.finite
    simpa only [RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe,
      Ideal.map_of_equiv] using
      (hI.map (S := R))

/-- Condition (APf) is invariant under an equivalence of coefficient rings. -/
theorem hasFiniteSubmoduleAdicCofinality_iff_of_ringEquiv
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (σ : R ≃+* S) (I : Ideal R) :
    I.HasFiniteSubmoduleAdicCofinality ↔
      (I.map σ.toRingHom).HasFiniteSubmoduleAdicCofinality := by
  constructor
  · intro hI
    let : Algebra R S := σ.toRingHom.toAlgebra
    let : Module.Finite R S := σ.finite
    simpa only [RingHom.algebraMap_toAlgebra] using
      (hI.map (S := S))
  · intro hI
    let : Algebra S R := σ.symm.toRingHom.toAlgebra
    let : Module.Finite S R := σ.symm.finite
    simpa only [RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe,
      Ideal.map_of_equiv] using
      (hI.map (S := R))

private theorem exists_fg_localizing_submodule
    {A : Type uA} [CommRing A] [Algebra R A]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Finite A M]
    (S : Submonoid R) [IsLocalization S A] :
    ∃ P : Submodule R M, P.FG ∧ IsLocalizedModule S P.subtype := by
  let : IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) := isLocalizedModule_id S M A
  obtain ⟨P, hP, hPloc⟩ := Submodule.FG.exists_localized'_eq S
    (LinearMap.id : M →ₗ[R] M) (Module.Finite.fg_top (R := A) (M := M))
  let e : P.localized' A S (LinearMap.id : M →ₗ[R] M) ≃ₗ[R] M :=
    ((LinearEquiv.ofEq _ _ hPloc).trans Submodule.topEquiv).restrictScalars R
  have he : e.toLinearMap ∘ₗ P.toLocalized' A S (LinearMap.id : M →ₗ[R] M) =
      P.subtype := by
    ext x
    rfl
  refine ⟨P, hP, ?_⟩
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv S
    (P.toLocalized' A S (LinearMap.id : M →ₗ[R] M)) e

private theorem cofinal_le_of_isLocalizedModule
    {A : Type uA} [CommRing A] [Algebra R A]
    {X : Type*} [AddCommGroup X] [Module R X]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] (S : Submonoid R) [IsLocalization S A]
    (f : X →ₗ[R] M) [IsLocalizedModule S f]
    (I : Ideal R) (Q : Submodule R X) (N : Submodule A M)
    (hQ : Q.localized' A S f = N) (m n : ℕ)
    (h : Q ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • Q) :
    N ⊓ (((I.map (algebraMap R A)) ^ m) • (⊤ : Submodule A M)) ≤
      ((I.map (algebraMap R A)) ^ n) • N := by
  have hloc := (Submodule.localized'gi A S f).gc.monotone_l h
  simpa only [Submodule.localized'_inf, Submodule.localized'_smul,
    Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_pow, hQ] using hloc

/-- Submodule adic cofinality passes to the extension of an ideal along an
arbitrary localization algebra. This is localization stability of condition (AP)
of Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4. Neither the ideal nor
the submodules need be finitely generated; no finiteness of the localization
algebra over the original ring is required. -/
theorem HasSubmoduleAdicCofinality.map_of_isLocalization
    {A : Type uA} [CommRing A] [Algebra R A]
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality)
    (S : Submonoid R) [IsLocalization S A] :
    (I.map (algebraMap R A)).HasSubmoduleAdicCofinality := by
  refine (hasSubmoduleAdicCofinality_iff _).2 ?_
  intro M _ _ _ N n
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  obtain ⟨P, hP, hPloc⟩ := exists_fg_localizing_submodule (A := A) (M := M) S
  let : Module.Finite R P := Module.Finite.of_fg hP
  let : IsLocalizedModule S P.subtype := hPloc
  let Q := (N.restrictScalars R).comap P.subtype
  have hQ : Q.localized' A S P.subtype = N :=
    (Submodule.localized'gi A S P.subtype).l_u_eq N
  obtain ⟨m, hm⟩ := hI.cofinal Q n
  exact ⟨m, cofinal_le_of_isLocalizedModule S P.subtype I Q N hQ m n hm⟩

/-- Finite-submodule adic cofinality passes to the extension of an ideal along an
arbitrary localization algebra. This is localization stability of condition (APf)
of Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4. No finite generation
of the ideal or finiteness of the localization algebra over the original ring
is required. -/
theorem HasFiniteSubmoduleAdicCofinality.map_of_isLocalization
    {A : Type uA} [CommRing A] [Algebra R A]
    {I : Ideal R} (hI : I.HasFiniteSubmoduleAdicCofinality)
    (S : Submonoid R) [IsLocalization S A] :
    (I.map (algebraMap R A)).HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff _).2 ?_
  intro M _ _ _ N hN n
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  obtain ⟨P, hP, hPloc⟩ := exists_fg_localizing_submodule (A := A) (M := M) S
  let : Module.Finite R P := Module.Finite.of_fg hP
  let : IsLocalizedModule S P.subtype := hPloc
  obtain ⟨Q, hQfg, hQ⟩ := Submodule.FG.exists_localized'_eq S P.subtype hN
  obtain ⟨m, hm⟩ := hI.cofinal Q hQfg n
  exact ⟨m, cofinal_le_of_isLocalizedModule S P.subtype I Q N hQ m n hm⟩

/-- Nilpotent ideals have submodule adic cofinality: a single vanishing power
works for every submodule and every index. No Noetherianity or finite generation
of the ideal or submodule is required. -/
theorem hasSubmoduleAdicCofinality_of_isNilpotent
    (I : Ideal R) (hI : IsNilpotent I) :
    I.HasSubmoduleAdicCofinality := by
  obtain ⟨k, hk⟩ := hI
  refine (hasSubmoduleAdicCofinality_iff I).2 ?_
  intro X _ _ _ K n
  refine ⟨k, ?_⟩
  rw [hk, zero_smul, Submodule.zero_eq_bot, inf_bot_eq]
  exact bot_le

/-- Nilpotent ideals have finite-submodule adic cofinality, as a consequence of
full submodule adic cofinality. -/
theorem hasFiniteSubmoduleAdicCofinality_of_isNilpotent
    (I : Ideal R) (hI : IsNilpotent I) :
    I.HasFiniteSubmoduleAdicCofinality :=
  (hasSubmoduleAdicCofinality_of_isNilpotent I hI).hasFiniteSubmoduleAdicCofinality

end Ideal


/-! ## Products and intersections of ideals with submodule-adic cofinality -/

@[expose] public section

/-- The product of two ideals with submodule-adic cofinality has
submodule-adic cofinality. -/
theorem _root_.Ideal.HasSubmoduleAdicCofinality.mul {R : Type*} [CommRing R] {I J : Ideal R}
    (hI : I.HasSubmoduleAdicCofinality)
    (hJ : J.HasSubmoduleAdicCofinality) :
    (I * J).HasSubmoduleAdicCofinality := by
  intro M _ _ _ N n
  obtain ⟨b, hb⟩ :
      ∃ b : ℕ, N ⊓ (J ^ b) • (⊤ : Submodule R M) ≤ (J ^ n) • N := by
    apply hJ
  obtain ⟨a, ha⟩ :
      ∃ a : ℕ,
        ((J ^ n) • N) ⊓ (I ^ a) • (⊤ : Submodule R M) ≤
          (I ^ n) • ((J ^ n) • N) := by
    apply hI
  refine ⟨max a b, ?_⟩
  simpa only [mul_pow] using
    Submodule.inf_mul_pow_smul_le_of_inf_smul_le I J N a b n n hb ha

/-- Finite-submodule cofinality for the right ideal and arbitrary-submodule
cofinality for the left ideal imply finite-submodule cofinality for their
product. No finite-generation hypothesis is needed for the intermediate
submodule. -/
theorem _root_.Ideal.HasFiniteSubmoduleAdicCofinality.mul_of_left
    {R : Type*} [CommRing R] {I J : Ideal R}
    (hJ : J.HasFiniteSubmoduleAdicCofinality)
    (hI : I.HasSubmoduleAdicCofinality) :
    (I * J).HasFiniteSubmoduleAdicCofinality := by
  intro M _ _ _ N hN n
  obtain ⟨b, hb⟩ :
      ∃ b : ℕ, N ⊓ (J ^ b) • (⊤ : Submodule R M) ≤ (J ^ n) • N := by
    apply hJ
    exact hN
  obtain ⟨a, ha⟩ :
      ∃ a : ℕ,
        ((J ^ n) • N) ⊓ (I ^ a) • (⊤ : Submodule R M) ≤
          (I ^ n) • ((J ^ n) • N) := by
    apply hI
  refine ⟨max a b, ?_⟩
  simpa only [mul_pow] using
    Submodule.inf_mul_pow_smul_le_of_inf_smul_le I J N a b n n hb ha

/-- The intersection of two ideals with submodule-adic cofinality has
submodule-adic cofinality. -/
theorem _root_.Ideal.HasSubmoduleAdicCofinality.inf {R : Type*} [CommRing R] {I J : Ideal R}
    (hI : I.HasSubmoduleAdicCofinality)
    (hJ : J.HasSubmoduleAdicCofinality) :
    (I ⊓ J).HasSubmoduleAdicCofinality := by
  have hprod : (I * J).HasSubmoduleAdicCofinality := hI.mul hJ
  intro M _ _ _ N
  refine
    (Submodule.forall_exists_inf_pow_smul_le_iff_of_pow_cofinal
      (I * J) (I ⊓ J) N ?_ ?_).mp ?_
  · intro n
    refine ⟨n, ?_⟩
    exact pow_le_pow_left' (le_inf Ideal.mul_le_left Ideal.mul_le_right) n
  · intro n
    refine ⟨2 * n, ?_⟩
    calc
      (I ⊓ J) ^ (2 * n) = (I ⊓ J) ^ n * (I ⊓ J) ^ n := by
        rw [two_mul, pow_add]
      _ ≤ I ^ n * J ^ n :=
        mul_le_mul' (pow_le_pow_left' inf_le_left n)
          (pow_le_pow_left' inf_le_right n)
      _ = (I * J) ^ n := (mul_pow I J n).symm
  · intro n
    apply hprod

/-- Finite-submodule cofinality for the right ideal and arbitrary-submodule
cofinality for the left ideal imply finite-submodule cofinality for their
intersection. The cofinality comparison is made at the original submodule. -/
theorem _root_.Ideal.HasFiniteSubmoduleAdicCofinality.inf_of_left
    {R : Type*} [CommRing R] {I J : Ideal R}
    (hJ : J.HasFiniteSubmoduleAdicCofinality)
    (hI : I.HasSubmoduleAdicCofinality) :
    (I ⊓ J).HasFiniteSubmoduleAdicCofinality := by
  have hprod : (I * J).HasFiniteSubmoduleAdicCofinality := hJ.mul_of_left hI
  intro M _ _ _ N hN
  refine
    (Submodule.forall_exists_inf_pow_smul_le_iff_of_pow_cofinal
      (I * J) (I ⊓ J) N ?_ ?_).mp ?_
  · intro n
    refine ⟨n, ?_⟩
    exact pow_le_pow_left' (le_inf Ideal.mul_le_left Ideal.mul_le_right) n
  · intro n
    refine ⟨2 * n, ?_⟩
    calc
      (I ⊓ J) ^ (2 * n) = (I ⊓ J) ^ n * (I ⊓ J) ^ n := by
        rw [two_mul, pow_add]
      _ ≤ I ^ n * J ^ n :=
        mul_le_mul' (pow_le_pow_left' inf_le_left n)
          (pow_le_pow_left' inf_le_right n)
      _ = (I * J) ^ n := (mul_pow I J n).symm
  · intro n
    apply hprod
    exact hN
@[expose] public section

/-- Submodule adic cofinality is preserved by a binary ideal supremum.
Neither ideal nor the test submodule must be finitely generated. -/
theorem _root_.Ideal.HasSubmoduleAdicCofinality.sup
    {R : Type*} [CommRing R] {I J : _root_.Ideal R}
    (hI : I.HasSubmoduleAdicCofinality) (hJ : J.HasSubmoduleAdicCofinality) :
    (I ⊔ J).HasSubmoduleAdicCofinality := by
  intro M _ _ _ N n
  obtain ⟨b, hb⟩ := hJ.cofinal N n
  obtain ⟨a, ha⟩ := hI.cofinal
    (N.map (((J ^ b) • (⊤ : Submodule R M)).mkQ)) n
  refine ⟨a + b,
    (Submodule.inf_sup_pow_smul_le_sup_of_quotient I J N n a b hb ha).trans ?_⟩
  have hIle : I ^ n ≤ (I ⊔ J) ^ n := pow_le_pow_left' le_sup_left n
  have hJle : J ^ n ≤ (I ⊔ J) ^ n := pow_le_pow_left' le_sup_right n
  refine sup_le ?_ ?_
  · refine Submodule.smul_le.2 ?_
    intro r hr z hz
    exact Submodule.smul_mem_smul (hIle hr) hz
  · refine Submodule.smul_le.2 ?_
    intro r hr z hz
    exact Submodule.smul_mem_smul (hJle hr) hz

/-- Finite-submodule adic cofinality is preserved by a binary ideal supremum.
Only the test submodule, not either ideal, is required to be finitely generated. -/
theorem _root_.Ideal.HasFiniteSubmoduleAdicCofinality.sup
    {R : Type*} [CommRing R] {I J : _root_.Ideal R}
    (hI : I.HasFiniteSubmoduleAdicCofinality)
    (hJ : J.HasFiniteSubmoduleAdicCofinality) :
    (I ⊔ J).HasFiniteSubmoduleAdicCofinality := by
  intro M _ _ _ N hN n
  obtain ⟨b, hb⟩ := hJ.cofinal N hN n
  obtain ⟨a, ha⟩ := hI.cofinal
    (N.map (((J ^ b) • (⊤ : Submodule R M)).mkQ)) (hN.map _) n
  refine ⟨a + b,
    (Submodule.inf_sup_pow_smul_le_sup_of_quotient I J N n a b hb ha).trans ?_⟩
  have hIle : I ^ n ≤ (I ⊔ J) ^ n := pow_le_pow_left' le_sup_left n
  have hJle : J ^ n ≤ (I ⊔ J) ^ n := pow_le_pow_left' le_sup_right n
  refine sup_le ?_ ?_
  · refine Submodule.smul_le.2 ?_
    intro r hr z hz
    exact Submodule.smul_mem_smul (hIle hr) hz
  · refine Submodule.smul_le.2 ?_
    intro r hr z hz
    exact Submodule.smul_mem_smul (hJle hr) hz

/-- A finite supremum of ideals with submodule adic cofinality has submodule
adic cofinality. The indexing type is arbitrary and the empty supremum is allowed. -/
theorem _root_.Ideal.HasSubmoduleAdicCofinality.finset_sup
    {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (I : ι → _root_.Ideal R)
    (hI : ∀ i ∈ s, (I i).HasSubmoduleAdicCofinality) :
    (s.sup I).HasSubmoduleAdicCofinality := by
  classical
  revert hI
  induction s using Finset.induction_on with
  | empty =>
      intro _ M _ _ _ N n
      exact ⟨1, by simp⟩
  | @insert i s _ ih =>
      intro hI
      simpa only [Finset.sup_insert] using
        (hI i (Finset.mem_insert_self i s)).sup
          (ih fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))

/-- A finite supremum of ideals with finite-submodule adic cofinality has
finite-submodule adic cofinality, including the empty supremum. -/
theorem _root_.Ideal.HasFiniteSubmoduleAdicCofinality.finset_sup
    {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (I : ι → _root_.Ideal R)
    (hI : ∀ i ∈ s, (I i).HasFiniteSubmoduleAdicCofinality) :
    (s.sup I).HasFiniteSubmoduleAdicCofinality := by
  classical
  revert hI
  induction s using Finset.induction_on with
  | empty =>
      intro _ M _ _ _ N _ n
      exact ⟨1, by simp⟩
  | @insert i s _ ih =>
      intro hI
      simpa only [Finset.sup_insert] using
        (hI i (Finset.mem_insert_self i s)).sup
          (ih fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))
