/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Scalar extension of submodules

Scalar extension carries the action of an ideal on a submodule to the action of
its extended ideal on the extended submodule. The coefficient semiring is
commutative, but the scalar algebra need not be. No flatness or finiteness
hypothesis is required, and the module may be only an additive commutative monoid.

Centrality of the algebra map allows its image to commute with the left-factor
scalar action on the tensor product.

An `R`-linear map from the scalar algebra to `R` taking `1` to `1` contracts
extended submodules along `m ↦ 1 ⊗ m`, and hence reflects submodule inclusions.
The map need not preserve multiplication.

Over a commutative coefficient ring, injectivity of tensor units on modules in
the maximum of the coefficient and module universes also contracts extended
submodules. Consequently scalar extension reflects submodule inclusions and
finite generation of submodules, without requiring a flat scalar algebra.

## References

The formalization uses Mathlib's submodule base change, ideal map, ideal action,
span induction, tensor balancing, quotient isomorphism, tensor right-exactness
and finite span APIs.
-/

@[expose] public section

universe uR uA uS uM

open scoped Pointwise TensorProduct

namespace Submodule

private theorem map_baseChange_restrictScalars_le
    {R : Type uR} {S : Type uS} [CommSemiring R] [Semiring S]
    [Algebra R S] {M : Type uM} [AddCommMonoid M] [Module R M]
    (p : S →ₗ[R] R) (N : Submodule R M) :
    ((N.baseChange S).restrictScalars R).map
      ((TensorProduct.lid R M).toLinearMap.comp (p.rTensor M)) ≤ N := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ LinearMap.range (N.subtype.baseChange S) at hx
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul s n =>
    change p s • (n : M) ∈ N
    exact N.smul_mem (p s) n.property
  | add x y hx hy =>
    simpa only [map_add] using N.add_mem hx hy

/-- An `R`-linear map from `S` to `R` taking `1` to `1` contracts membership in
an extended submodule along `m ↦ 1 ⊗ m`. The scalar algebra need not be
commutative, and the map need not preserve multiplication. -/
theorem one_tmul_mem_baseChange_iff_of_linearRetraction
    {R : Type uR} {S : Type uS} [CommSemiring R] [Semiring S]
    [Algebra R S] {M : Type uM} [AddCommMonoid M] [Module R M]
    (p : S →ₗ[R] R) (hp : p (1 : S) = 1) (N : Submodule R M) (m : M) :
    (1 : S) ⊗ₜ[R] m ∈ N.baseChange S ↔ m ∈ N := by
  constructor
  · intro hm
    have hm' : ((TensorProduct.lid R M).toLinearMap.comp (p.rTensor M))
        ((1 : S) ⊗ₜ[R] m) ∈ N :=
      map_baseChange_restrictScalars_le p N (mem_map_of_mem hm)
    change p (1 : S) • m ∈ N at hm'
    simpa only [hp, one_smul] using hm'
  · intro hm
    exact tmul_mem_baseChange_of_mem (A := S) 1 hm

/-- Scalar extension reflects submodule inclusions when there is an `R`-linear
map from `S` to `R` taking `1` to `1`. No flatness or commutativity of `S` is
required. -/
theorem baseChange_le_iff_of_linearRetraction
    {R : Type uR} {S : Type uS} [CommSemiring R] [Semiring S]
    [Algebra R S] {M : Type uM} [AddCommMonoid M] [Module R M]
    (p : S →ₗ[R] R) (hp : p (1 : S) = 1) (N K : Submodule R M) :
    N.baseChange S ≤ K.baseChange S ↔ N ≤ K := by
  constructor
  · intro h m hm
    exact (one_tmul_mem_baseChange_iff_of_linearRetraction p hp K m).mp
      (h (tmul_mem_baseChange_of_mem (A := S) 1 hm))
  · exact baseChange_mono S

/-- Scalar extension commutes with the action of an ideal on a submodule, using
its extended ideal and the canonical left-factor action on the tensor product.
The scalar algebra need not be commutative; no flatness or finiteness is needed. -/
theorem baseChange_smul
    {R : Type uR} {A : Type uA} [CommSemiring R] [Semiring A]
    [Algebra R A] {M : Type uM} [AddCommMonoid M] [Module R M]
    (I : Ideal R) (N : Submodule R M) :
    (I • N).baseChange A = (I.map (algebraMap R A)) • N.baseChange A := by
  apply le_antisymm
  · rw [baseChange_eq_span]
    refine span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    change (1 : A) ⊗ₜ[R] m ∈ (I.map (algebraMap R A)) • N.baseChange A
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr m hm
      simpa only [TensorProduct.mk_apply, IsScalarTower.algebraMap_smul,
        TensorProduct.tmul_smul] using
        (smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R A) hr)
          (tmul_mem_baseChange_of_mem (A := A) 1 hm))
    · intro x y hx hy
      simpa only [TensorProduct.tmul_add] using
        ((I.map (algebraMap R A)) • N.baseChange A).add_mem hx hy
  · refine smul_le.mpr fun a ha x hx => ?_
    change a ∈ span A (algebraMap R A '' (I : Set R)) at ha
    refine span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨r, hr, rfl⟩
      rw [baseChange_eq_span] at hx
      refine span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨m, hm, rfl⟩
        simpa only [TensorProduct.mk_apply, IsScalarTower.algebraMap_smul,
          TensorProduct.tmul_smul] using
          (tmul_mem_baseChange_of_mem (A := A) 1 (smul_mem_smul hr hm))
      · simpa only [smul_zero] using ((I • N).baseChange A).zero_mem
      · intro y z _ _ hy hz
        simpa only [smul_add] using ((I • N).baseChange A).add_mem hy hz
      · intro b y _ hy
        rw [IsScalarTower.algebraMap_smul, smul_comm r b]
        exact ((I • N).baseChange A).smul_mem b
          (by simpa only [IsScalarTower.algebraMap_smul] using hy)
    · simpa only [zero_smul] using ((I • N).baseChange A).zero_mem
    · intro b c _ _ hb hc
      simpa only [add_smul] using ((I • N).baseChange A).add_mem hb hc
    · intro b c _ hc
      simpa only [smul_eq_mul, mul_smul] using ((I • N).baseChange A).smul_mem b hc

/-- Injectivity of the tensor unit reflects membership in extended submodules.
The scalar algebra need not be commutative or flat. -/
theorem one_tmul_mem_baseChange_iff_of_injective
    {R : Type uR} {S : Type uS} [CommRing R] [Semiring S]
    [Algebra R S] {M : Type uM} [AddCommMonoid M] [Module R M]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1))
    (N : Submodule R M) (m : M) :
    (1 : S) ⊗ₜ[R] m ∈ N.baseChange S ↔ m ∈ N := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup S := Module.addCommMonoidToAddCommGroup R
  -- The free cover puts the quotient in the universe tested by `hunit`.
  let F := M →₀ R
  let p : F →ₗ[R] M := Finsupp.linearCombination R id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective R M
  let P₀ : Submodule R F := N.comap p
  let C := F ⧸ P₀
  have hker : P₀ = LinearMap.ker (N.mkQ.comp p) := by
    rw [LinearMap.ker_comp, ker_mkQ]
  let e : C ≃ₗ[R] M ⧸ N :=
    (quotEquivOfEq P₀ _ hker).trans
      ((N.mkQ.comp p).quotKerEquivOfSurjective (N.mkQ_surjective.comp hp))
  have hquot : Function.Injective (TensorProduct.mk R S (M ⧸ N) 1) := by
    intro x y hxy
    apply e.symm.injective
    apply hunit C
    have hnatural := LinearMap.lTensor_comp_mk (M := S) e.symm.toLinearMap (1 : S)
    calc
      TensorProduct.mk R S C 1 (e.symm x) =
          e.symm.toLinearMap.lTensor S (TensorProduct.mk R S (M ⧸ N) 1 x) :=
        (LinearMap.congr_fun hnatural x).symm
      _ = e.symm.toLinearMap.lTensor S (TensorProduct.mk R S (M ⧸ N) 1 y) :=
        congrArg _ hxy
      _ = TensorProduct.mk R S C 1 (e.symm y) := LinearMap.congr_fun hnatural y
  constructor
  · intro hm
    have hm' : (1 : S) ⊗ₜ[R] m ∈ LinearMap.ker (N.mkQ.lTensor S) := by
      rw [_root_.lTensor_mkQ S N]
      change (1 : S) ⊗ₜ[R] m ∈ LinearMap.range (N.subtype.baseChange S) at hm
      obtain ⟨x, hx⟩ := hm
      exact ⟨x, by simpa only [LinearMap.baseChange_eq_ltensor] using hx⟩
    have hzero : TensorProduct.mk R S (M ⧸ N) 1 (N.mkQ m) = 0 := by
      simpa only [LinearMap.mem_ker, LinearMap.lTensor_tmul, TensorProduct.mk_apply] using hm'
    have hq : N.mkQ m = 0 := hquot (by simpa only [map_zero] using hzero)
    exact (Submodule.Quotient.mk_eq_zero (p := N)).mp hq
  · exact tmul_mem_baseChange_of_mem (A := S) 1

/-- Injectivity of the tensor unit makes scalar extension reflect submodule
inclusions. The scalar algebra need not be commutative or flat. -/
theorem baseChange_le_iff_of_injective
    {R : Type uR} {S : Type uS} [CommRing R] [Semiring S]
    [Algebra R S] {M : Type uM} [AddCommMonoid M] [Module R M]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1))
    (N K : Submodule R M) :
    N.baseChange S ≤ K.baseChange S ↔ N ≤ K := by
  constructor
  · intro h m hm
    exact (one_tmul_mem_baseChange_iff_of_injective hunit K m).mp
      (h (tmul_mem_baseChange_of_mem (A := S) 1 hm))
  · exact baseChange_mono S

/-- Injectivity of the tensor unit makes finite generation invariant under
scalar extension of a submodule. No flatness is assumed. -/
theorem fg_baseChange_iff_of_injective
    {R : Type uR} {S : Type uS} [CommRing R] [Semiring S]
    [Algebra R S] {M : Type uM} [AddCommMonoid M] [Module R M]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1))
    (N : Submodule R M) : (N.baseChange S).FG ↔ N.FG := by
  constructor
  · intro hN
    rw [baseChange_eq_span, map_coe] at hN
    obtain ⟨s, hs, hspan⟩ := (fg_span_iff_fg_span_finset_subset _).mp hN
    obtain ⟨t, htN, ht, hspan'⟩ :=
      (Set.exists_subset_image_finite_and
        (f := TensorProduct.mk R S M 1) (s := (N : Set M))
        (p := fun t => span S (TensorProduct.mk R S M 1 '' (N : Set M)) =
          span S t)).mp ⟨(s : Set (S ⊗[R] M)), hs, s.finite_toSet, hspan⟩
    let N₀ : Submodule R M := span R t
    have hbase : N₀.baseChange S = N.baseChange S := by
      dsimp only [N₀]
      rw [baseChange_span, baseChange_eq_span, map_coe]
      exact hspan'.symm
    have hN₀ : N₀ = N :=
      le_antisymm (span_le.mpr htN)
        ((baseChange_le_iff_of_injective hunit N N₀).mp hbase.ge)
    rw [← hN₀]
    exact fg_span ht
  · intro hN
    let : Module.Finite R N := Module.Finite.of_fg hN
    exact Module.Finite.iff_fg.mp
      (Module.Finite.of_surjective (N.toBaseChange S) (N.toBaseChange_surjective S))

end Submodule
