/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Annihilators and ideal-power bounds on modules

A surjective semilinear map carries annihilating scalars to annihilating scalars. For an
injective semilinear map, a scalar whose image annihilates the target annihilates the source.
For a bijective semilinear map, the source annihilator is the comap of the target annihilator.

These results generalize `LinearMap.annihilator_le_of_surjective`,
`LinearMap.annihilator_le_of_injective`, and `LinearEquiv.annihilator_eq` in
`Mathlib.RingTheory.Ideal.Maps`. The proofs follow their elementwise arguments.

Radical containment after adding the annihilator gives a uniform ideal-power bound
on the original module when the image of the source ideal in the annihilator
quotient is finitely generated. The quotient is used only for ideal algebra; no
quotient-ring action on the module is introduced. Exponents may be zero.
-/

@[expose] public section

universe uR uS uM uN

namespace LinearMap

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] {ρ : R →+* S}

/-- Along a surjective semilinear map, every scalar annihilating the source has image
annihilating the target. -/
theorem annihilator_le_comap_of_surjective (f : M →ₛₗ[ρ] N)
    (hf : Function.Surjective f) :
    Module.annihilator R M ≤ Ideal.comap ρ (Module.annihilator S N) := by
  intro r hr
  rw [Module.mem_annihilator] at hr
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro n
  obtain ⟨m, rfl⟩ := hf n
  rw [← f.map_smulₛₗ, hr, f.map_zero]

/-- Along an injective semilinear map, a scalar whose image annihilates the target
annihilates the source. -/
theorem comap_annihilator_le_of_injective (f : M →ₛₗ[ρ] N)
    (hf : Function.Injective f) :
    Ideal.comap ρ (Module.annihilator S N) ≤ Module.annihilator R M := by
  intro r hr
  rw [Ideal.mem_comap, Module.mem_annihilator] at hr
  rw [Module.mem_annihilator]
  intro m
  apply hf
  rw [f.map_smulₛₗ, hr, f.map_zero]

/-- A bijective semilinear map identifies the source annihilator with the comap of the
target annihilator. -/
theorem annihilator_eq_comap_of_bijective (f : M →ₛₗ[ρ] N)
    (hf : Function.Bijective f) :
    Module.annihilator R M = Ideal.comap ρ (Module.annihilator S N) :=
  (f.annihilator_le_comap_of_surjective hf.2).antisymm
    (f.comap_annihilator_le_of_injective hf.1)

end LinearMap

section CommRing

universe uPowerR uPowerM

namespace Ideal

/-- Effective radical containment gives an ideal-power bound on a module if the image
of the source ideal in the annihilator quotient is finitely generated. The original
ideal need not be finitely generated, and the module need not be Noetherian. -/
theorem exists_pow_smul_top_le_of_radical_sup_annihilator_le_of_map_fg
    {R : Type uPowerR} [CommRing R]
    {M : Type uPowerM} [AddCommMonoid M] [Module R M] {I J : Ideal R}
    (hfg : (I.map (Ideal.Quotient.mk (Module.annihilator R M))).FG)
    (h : (I ⊔ Module.annihilator R M).radical ≤
      (J ⊔ Module.annihilator R M).radical) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) ≤ J • ⊤ := by
  let A := Module.annihilator R M
  let q := Ideal.Quotient.mk A
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have himage : I.map q ≤ (J.map q).radical := by
    calc
      I.map q ≤ (I ⊔ A).radical.map q :=
        Ideal.map_mono (le_sup_left.trans Ideal.le_radical)
      _ ≤ (J ⊔ A).radical.map q := Ideal.map_mono h
      _ = (J.map q).radical := by
        rw [Ideal.map_radical_of_surjective hq (by simp [q]), Ideal.map_sup]
        simp [q]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg himage hfg
  have hpow : I ^ n ≤ J ⊔ A := by
    have hmap : (I ^ n).map q ≤ J.map q := by
      simpa only [Ideal.map_pow] using hn
    simpa [q, sup_comm] using (Ideal.map_le_iff_le_comap.mp hmap)
  refine ⟨n, Submodule.smul_le.mpr ?_⟩
  intro r hr m hm
  rcases Submodule.mem_sup.mp (hpow hr) with ⟨j, hj, a, ha, rfl⟩
  rw [add_smul, (Module.mem_annihilator.mp ha) m, add_zero]
  exact Submodule.smul_mem_smul hj hm

end Ideal

end CommRing
