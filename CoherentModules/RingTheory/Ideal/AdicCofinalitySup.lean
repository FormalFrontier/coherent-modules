/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Ideal-power bounds from a quotient

A bound on the intersection with a power of one ideal, together with a power bound
in the corresponding module quotient, controls the intersection with a power of
the supremum of two ideals.
-/

@[expose] public section

namespace Submodule

universe uR uM

variable {R : Type uR} [CommRing R] {M : Type uM} [AddCommGroup M] [Module R M]

/-- Bounds at the `J`-cut and on the image in its quotient give a bound by the
sum of the separate `I`- and `J`-powers of `N`. The quotient retains its original
`R`-module structure, and the exponents may be zero. -/
theorem inf_sup_pow_smul_le_sup_of_quotient
    (I J : Ideal R) (N : Submodule R M) (n a b : ℕ)
    (hJ : N ⊓ (J ^ b) • (⊤ : Submodule R M) ≤ (J ^ n) • N)
    (hI : N.map (((J ^ b) • (⊤ : Submodule R M)).mkQ) ⊓
        (I ^ a) • (⊤ : Submodule R (M ⧸ ((J ^ b) • (⊤ : Submodule R M)))) ≤
      (I ^ n) • N.map (((J ^ b) • (⊤ : Submodule R M)).mkQ)) :
    N ⊓ ((I ⊔ J) ^ (a + b)) • (⊤ : Submodule R M) ≤
      (I ^ n) • N ⊔ (J ^ n) • N := by
  let T : Submodule R M := (J ^ b) • (⊤ : Submodule R M)
  let q : M →ₗ[R] M ⧸ T := T.mkQ
  change N ⊓ T ≤ (J ^ n) • N at hJ
  change N.map q ⊓ (I ^ a) • (⊤ : Submodule R (M ⧸ T)) ≤
    (I ^ n) • N.map q at hI
  have hpow : (I ⊔ J) ^ (a + b) ≤ I ^ a ⊔ J ^ b :=
    Ideal.sup_pow_add_le_pow_sup_pow
  have hcut : ((I ⊔ J) ^ (a + b)) • (⊤ : Submodule R M) ≤
      ((I ^ a) • (⊤ : Submodule R (M ⧸ T))).comap q := by
    refine Submodule.smul_le.2 ?_
    intro r hr z hz
    change q (r • z) ∈ (I ^ a) • (⊤ : Submodule R (M ⧸ T))
    rcases Submodule.mem_sup.mp (hpow hr) with ⟨s, hs, t, ht, rfl⟩
    have htz : t • z ∈ T := by
      change t • z ∈ (J ^ b) • (⊤ : Submodule R M)
      apply Submodule.smul_mem_smul
      · exact ht
      · exact hz
    have hqtz : q (t • z) = 0 := by
      have hker : t • z ∈ LinearMap.ker q := by
        simpa only [q, Submodule.ker_mkQ] using htz
      exact hker
    rw [add_smul, map_add, hqtz, add_zero, map_smul]
    apply Submodule.smul_mem_smul
    · exact hs
    · trivial
  intro x hx
  have hqx : q x ∈ (I ^ n) • N.map q :=
    hI ⟨Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩, hcut hx.2⟩
  have hqxmap : q x ∈ ((I ^ n) • N).map q := by
    rw [Submodule.map_smul'' (I ^ n) N q]
    exact hqx
  rcases Submodule.mem_map.mp hqxmap with ⟨y, hy, hyq⟩
  have hIN : (I ^ n) • N ≤ N := by
    refine Submodule.smul_le.2 ?_
    intro r _ z hz
    exact N.smul_mem r hz
  have hdiffT : x - y ∈ T := by
    have hzero : q (x - y) = 0 := by
      rw [map_sub, hyq, sub_self]
    have hker : x - y ∈ LinearMap.ker q := hzero
    simpa only [q, Submodule.ker_mkQ] using hker
  have hdiffJ : x - y ∈ (J ^ n) • N :=
    hJ ⟨N.sub_mem hx.1 (hIN hy), hdiffT⟩
  have hJle : (J ^ n) • N ≤ (I ^ n) • N ⊔ (J ^ n) • N := le_sup_right
  have hIle : (I ^ n) • N ≤ (I ^ n) • N ⊔ (J ^ n) • N := le_sup_left
  have hsum : (x - y) + y ∈ (I ^ n) • N ⊔ (J ^ n) • N :=
    ((I ^ n) • N ⊔ (J ^ n) • N).add_mem (hJle hdiffJ) (hIle hy)
  simpa only [sub_add_cancel] using hsum

end Submodule
