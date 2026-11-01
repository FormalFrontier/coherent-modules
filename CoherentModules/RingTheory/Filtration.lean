/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

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

## References

The Artin–Rees lemma and its stable-filtration proof are formalized by Andrew Yang
in `Mathlib.RingTheory.Filtration`. We apply that theorem over the annihilator
quotient, using this library's annihilator-quotient Noetherianity theorem and
Mathlib's quotient-module and scalar-restriction APIs.
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

end Ideal
