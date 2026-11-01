/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Pointwise bounds for products and power-cofinal ideals

A bound for each of two successive ideal-power cuts gives a bound for a
single cut by a power of their product. Mutual cofinality of ideal powers
also transports the pointwise existence of such bounds on a submodule.
-/

@[expose] public section

universe uR uM

namespace Submodule

variable {R : Type uR} [CommSemiring R] {M : Type uM}
  [AddCommMonoid M] [Module R M]

/-- Bounds for a `J`-power cut of `N` and an `I`-power cut of the resulting
submodule combine into a bound for a single product-power cut of `N`.
All four exponents may be zero. -/
theorem inf_mul_pow_smul_le_of_inf_smul_le
    (I J : Ideal R) (N : Submodule R M) (a b p q : ℕ)
    (hJ : N ⊓ (J ^ b) • (⊤ : Submodule R M) ≤ (J ^ q) • N)
    (hI : ((J ^ q) • N) ⊓ (I ^ a) • (⊤ : Submodule R M) ≤
      (I ^ p) • ((J ^ q) • N)) :
    N ⊓ ((I * J) ^ (max a b)) • (⊤ : Submodule R M) ≤
      ((I ^ p) * (J ^ q)) • N := by
  have hpowI : (I * J) ^ (max a b) ≤ I ^ a := by
    calc
      (I * J) ^ (max a b) ≤ I ^ (max a b) :=
        pow_le_pow_left' (Ideal.mul_le_left : I * J ≤ I) _
      _ ≤ I ^ a := by
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left a b)
        rw [hc, pow_add]
        exact Ideal.mul_le_left
  have hpowJ : (I * J) ^ (max a b) ≤ J ^ b := by
    calc
      (I * J) ^ (max a b) ≤ J ^ (max a b) :=
        pow_le_pow_left' (Ideal.mul_le_right : I * J ≤ J) _
      _ ≤ J ^ b := by
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right a b)
        rw [hc, pow_add]
        exact Ideal.mul_le_left
  have hcutI : ((I * J) ^ (max a b)) • (⊤ : Submodule R M) ≤
      (I ^ a) • (⊤ : Submodule R M) := by
    refine Submodule.smul_le.mpr ?_
    intro r hr x hx
    exact Submodule.smul_mem_smul (hpowI hr) hx
  have hcutJ : ((I * J) ^ (max a b)) • (⊤ : Submodule R M) ≤
      (J ^ b) • (⊤ : Submodule R M) := by
    refine Submodule.smul_le.mpr ?_
    intro r hr x hx
    exact Submodule.smul_mem_smul (hpowJ hr) hx
  have hfirst : N ⊓ ((I * J) ^ (max a b)) • (⊤ : Submodule R M) ≤
      (J ^ q) • N :=
    (inf_le_inf_left N hcutJ).trans hJ
  calc
    N ⊓ ((I * J) ^ (max a b)) • (⊤ : Submodule R M) ≤
        ((J ^ q) • N) ⊓ (I ^ a) • (⊤ : Submodule R M) :=
      le_inf hfirst (inf_le_right.trans hcutI)
    _ ≤ (I ^ p) • ((J ^ q) • N) := hI
    _ = ((I ^ p) * (J ^ q)) • N := (mul_smul (I ^ p) (J ^ q) N).symm

/-- Mutually cofinal ideal powers give equivalent pointwise power-cut bounds
for a submodule. Both the ambient cut and the target bound are transported. -/
theorem forall_exists_inf_pow_smul_le_iff_of_pow_cofinal
    (I J : Ideal R) (N : Submodule R M)
    (hIJ : ∀ n : ℕ, ∃ m : ℕ, I ^ m ≤ J ^ n)
    (hJI : ∀ n : ℕ, ∃ m : ℕ, J ^ m ≤ I ^ n) :
    (∀ n : ℕ, ∃ m : ℕ,
      N ⊓ (I ^ m) • (⊤ : Submodule R M) ≤ (I ^ n) • N) ↔
    (∀ n : ℕ, ∃ m : ℕ,
      N ⊓ (J ^ m) • (⊤ : Submodule R M) ≤ (J ^ n) • N) := by
  constructor
  · intro h n
    obtain ⟨a, ha⟩ := hIJ n
    obtain ⟨b, hb⟩ := h a
    obtain ⟨c, hc⟩ := hJI b
    have hcut : (J ^ c) • (⊤ : Submodule R M) ≤
        (I ^ b) • (⊤ : Submodule R M) := by
      refine Submodule.smul_le.mpr ?_
      intro r hr x hx
      exact Submodule.smul_mem_smul (hc hr) hx
    have htarget : (I ^ a) • N ≤ (J ^ n) • N := by
      refine Submodule.smul_le.mpr ?_
      intro r hr x hx
      exact Submodule.smul_mem_smul (ha hr) hx
    exact ⟨c, (inf_le_inf_left N hcut).trans (hb.trans htarget)⟩
  · intro h n
    obtain ⟨a, ha⟩ := hJI n
    obtain ⟨b, hb⟩ := h a
    obtain ⟨c, hc⟩ := hIJ b
    have hcut : (I ^ c) • (⊤ : Submodule R M) ≤
        (J ^ b) • (⊤ : Submodule R M) := by
      refine Submodule.smul_le.mpr ?_
      intro r hr x hx
      exact Submodule.smul_mem_smul (hc hr) hx
    have htarget : (J ^ a) • N ≤ (I ^ n) • N := by
      refine Submodule.smul_le.mpr ?_
      intro r hr x hx
      exact Submodule.smul_mem_smul (ha hr) hx
    exact ⟨c, (inf_le_inf_left N hcut).trans (hb.trans htarget)⟩

end Submodule
