/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicKrull
public import CoherentModules.RingTheory.Noetherian
public import Mathlib.RingTheory.Filtration

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Artin–Rees for Noetherian modules

For a Noetherian module over an arbitrary commutative ring, the intersection of
an arbitrary submodule with the ideal-power filtration satisfies the full shifted
Artin–Rees equality. Neither the scalar ring nor the ideal needs a finiteness
hypothesis.

The proof passes to the quotient by the module's annihilator, which is a
Noetherian ring. The existing quotient action and the scalar-restriction
submodule order isomorphism preserve the original submodule, ideal powers and
both scalar products in the equality.

As a consequence, every ideal of a Noetherian ring has finite-submodule adic
cofinality, the condition (APf) of Fujiwara--Kato. The local Noetherian-module
Artin–Rees theorem remains available over an arbitrary commutative ring.

## References

The Artin–Rees lemma and its stable-filtration proof are formalized by Andrew Yang
in `Mathlib.RingTheory.Filtration`. We apply that theorem over the annihilator
quotient, using this library's annihilator-quotient Noetherianity theorem and
Mathlib's quotient-module and scalar-restriction APIs.
The Noetherian-ring cofinality consequence is the (APf) part of Fujiwara--Kato,
*Foundations of Rigid Geometry I*, arXiv:1308.4734v5, Proposition 0.7.4.14.
The Krull membership specialization below recovers the subtype-witness statement
of Mathlib's `Ideal.mem_iInf_smul_pow_eq_bot_iff` from the cofinality theorem in
`CoherentModules.RingTheory.Ideal.AdicKrull`.
-/

@[expose] public section

universe uR uM

namespace Ideal

/-- Artin–Rees for a Noetherian module over an arbitrary commutative ring.
No Noetherianity of the scalar ring or finite generation of the ideal is assumed.

This generalizes Mathlib's `Ideal.exists_pow_inf_eq_pow_smul`, formalized by
Andrew Yang, by passing to the quotient by the module's annihilator and
transporting the full equality along the scalar-restriction submodule lattice. -/
theorem exists_pow_inf_eq_pow_smul_of_isNoetherian
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    [IsNoetherian R M]
    (K : Submodule R M) :
    ∃ c : ℕ, ∀ n ≥ c,
      (I ^ n • (⊤ : Submodule R M)) ⊓ K =
        I ^ (n - c) • ((I ^ c • (⊤ : Submodule R M)) ⊓ K) := by
  let B := R ⧸ Module.annihilator R M
  let : Module B M := Module.quotientAnnihilator
  let : IsScalarTower R B M := (Module.isTorsionBySet_annihilator R M).isScalarTower
  have : IsNoetherianRing B := isNoetherianRing_quotient_annihilator M
  have : Module.Finite B M := Module.Finite.of_restrictScalars_finite R B M
  let e : Submodule B M ≃o Submodule R M :=
    Submodule.orderIsoOfAlgebraMapSurjective Ideal.Quotient.mk_surjective
  have hK : (e.symm K).restrictScalars R = K := e.apply_symm_apply K
  -- Fix both scalar rings so the transport also rewrites the nested scalar product.
  have hsmul (J : Ideal R) (N : Submodule B M) :
      (J.map (algebraMap R B) • N).restrictScalars R = J • N.restrictScalars R :=
    Submodule.restrictScalars_map_smul_eq (R := B) (S := R) J N
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (I.map (algebraMap R B)) (e.symm K)
  refine ⟨c, fun n hn => ?_⟩
  simpa only [← Ideal.map_pow, Submodule.restrictScalars_inf,
    hsmul, Submodule.restrictScalars_top, hK] using
    congrArg (Submodule.restrictScalars R) (hc n hn)

/-- Every ideal of a Noetherian ring has finite-submodule adic cofinality.
This follows from Artin–Rees, as in Fujiwara--Kato, *Foundations of Rigid
Geometry I*, Proposition 0.7.4.14. -/
theorem hasFiniteSubmoduleAdicCofinality_of_isNoetherianRing
    {R : Type uR} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    I.HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro X _ _ _ K _ n
  obtain ⟨c, hc⟩ := exists_pow_inf_eq_pow_smul_of_isNoetherian I K
  refine ⟨n + c, ?_⟩
  rw [inf_comm, hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

/-- The finite-submodule cofinality Krull theorem recovers Mathlib's
`Ideal.mem_iInf_smul_pow_eq_bot_iff` under its Noetherian-ring hypotheses,
including its subtype-valued fixing scalar. The proof specializes the cofinality
API and converts the membership-conjunction witness to an element of the ideal. -/
theorem mem_iInf_pow_smul_top_iff_of_isNoetherianRing
    {R : Type uR} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : M) :
    (x ∈ ⨅ n : ℕ, (I ^ n) • (⊤ : Submodule R M)) ↔
      ∃ a : I, (a : R) • x = x := by
  have hAPf := hasFiniteSubmoduleAdicCofinality_of_isNoetherianRing I
  exact (hAPf.mem_iInf_pow_smul_top_iff x).trans
    ⟨fun ⟨a, ha, hax⟩ => ⟨⟨a, ha⟩, hax⟩,
      fun ⟨a, hax⟩ => ⟨a, a.property, hax⟩⟩

end Ideal
