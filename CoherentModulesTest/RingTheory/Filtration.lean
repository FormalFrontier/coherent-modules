/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Filtration

/-!
# Artin–Rees and shifted cofinality

Under the Noetherian-ring and finite-module hypotheses of Mathlib's
`Ideal.exists_pow_inf_eq_pow_smul`, the module version supplies the same full
equality of the original submodules. We use that equality to obtain a single
shift relating the induced filtration on a submodule to its intrinsic ideal
powers. The module's Noetherianity is inferred from the original hypotheses.
-/

universe uR uM

example
    {R : Type uR} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (K : Submodule R M) :
    ∃ c : ℕ, ∀ k : ℕ,
      K ⊓ (I ^ (k + c) • (⊤ : Submodule R M)) ≤ I ^ k • K := by
  -- This is also the proposition of Mathlib's Artin–Rees theorem at I and K.
  have hAR : ∃ c : ℕ, ∀ n ≥ c,
      (I ^ n • (⊤ : Submodule R M)) ⊓ K =
        I ^ (n - c) • ((I ^ c • (⊤ : Submodule R M)) ⊓ K) :=
    Ideal.exists_pow_inf_eq_pow_smul_of_isNoetherian I K
  obtain ⟨c, hc⟩ := hAR
  refine ⟨c, fun k => ?_⟩
  rw [inf_comm, hc (k + c) (Nat.le_add_left c k), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right
