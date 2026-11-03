/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The corresponding commutative-ring theorem in Mathlib carries the notice:
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.LeftExact

/-!
# Left exactness of semilinear Hom

For an exact pair `U → V → M` with surjective second map, semilinear precomposition
is exact at `V →ₛₗ[σ] N`. The scalars are semirings, `U` and `V` are additive
commutative monoids, and only `M` must be an additive commutative group. The codomain
`N` may be an arbitrary additive commutative monoid, with a commuting scalar action
that makes the precomposition maps linear.

The fiber argument uses surjectivity to find a common additive inverse after applying
the map to `M`. Its images in `N` give a common additive inverse for two elements;
commutativity then makes those elements equal, without cancellation in `N`.

This uses Mathlib's `Function.Exact` interface, introduced by Antoine Chambert-Loir,
and its semilinear precomposition maps. It generalizes Nailin Guan's
`LinearMap.exact_lcomp_of_exact_of_surjective`, whose same-scalar,
commutative-ring, additive-group statement is a specialization.
-/

@[expose] public section

universe uR uR₂ uS uU uV uM uN

namespace LinearMap

/-- Semilinear precomposition takes an exact pair with surjective second map to an
exact pair. Only the surjective image `M` must be an additive group; no cancellation
in `N` or surjectivity of the scalar homomorphism is required. The scalar action of
`S` is needed only on `N`, where it commutes with the given `R₂`-action.

This generalizes `LinearMap.exact_lcomp_of_exact_of_surjective` from same-scalar Hom
over a commutative ring with additive groups to semilinear Hom over semirings. -/
theorem exact_lcompₛₗ_of_exact_of_surjective
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS}
    {U : Type uU} {V : Type uV} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring R₂] [Semiring S]
    [AddCommMonoid U] [AddCommMonoid V]
    [AddCommGroup M] [AddCommMonoid N]
    [Module R U] [Module R V] [Module R M]
    [Module R₂ N] [Module S N]
    (σ : R →+* R₂) [SMulCommClass R₂ S N]
    {f : U →ₗ[R] V} {g : V →ₗ[R] M}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.lcompₛₗ S N σ g)
      (LinearMap.lcompₛₗ S N σ f) := by
  intro ψ
  constructor
  · intro hψ
    have hker : ∀ v : V, g v = 0 → ψ v = 0 := by
      intro v hv
      obtain ⟨u, rfl⟩ := (hfg v).mp hv
      exact DFunLike.congr_fun hψ u
    have hfiber : ∀ v w : V, g v = g w → ψ v = ψ w := by
      intro v w hvw
      obtain ⟨z, hz⟩ := hg (-g v)
      have hvz : ψ v + ψ z = 0 := by
        rw [← ψ.map_add]
        apply hker
        rw [g.map_add, hz, add_neg_cancel]
      have hwz : ψ w + ψ z = 0 := by
        rw [← ψ.map_add]
        apply hker
        rw [g.map_add, hz, ← hvw, add_neg_cancel]
      -- A common additive inverse suffices; cancellation in `N` is not needed.
      calc
        ψ v = ψ v + 0 := (add_zero _).symm
        _ = ψ v + (ψ z + ψ w) := by rw [add_comm (ψ z) (ψ w), hwz]
        _ = (ψ v + ψ z) + ψ w := (add_assoc _ _ _).symm
        _ = ψ w := by rw [hvz, zero_add]
    let desc : M → N := fun m => ψ (Function.surjInv hg m)
    have hdesc : ∀ v : V, desc (g v) = ψ v := by
      intro v
      exact hfiber _ v (Function.surjInv_eq hg (g v))
    let φ : M →ₛₗ[σ] N :=
      { toFun := desc
        map_add' := by
          intro m m'
          calc
            desc (m + m') =
                desc (g (Function.surjInv hg m + Function.surjInv hg m')) := by
              rw [g.map_add, Function.surjInv_eq hg m, Function.surjInv_eq hg m']
            _ = ψ (Function.surjInv hg m + Function.surjInv hg m') := hdesc _
            _ = desc m + desc m' := ψ.map_add _ _
        map_smul' := by
          intro r m
          calc
            desc (r • m) = desc (g (r • Function.surjInv hg m)) := by
              rw [g.map_smul, Function.surjInv_eq hg m]
            _ = ψ (r • Function.surjInv hg m) := hdesc _
            _ = σ r • desc m := ψ.map_smulₛₗ r _ }
    refine ⟨φ, ?_⟩
    ext v
    exact hdesc v
  · rintro ⟨φ, rfl⟩
    ext u
    change φ (g (f u)) = 0
    rw [(hfg (f u)).mpr ⟨u, rfl⟩, map_zero]

-- The commutative-ring statement follows with its given additive and module structures.
private theorem exact_lcomp_commRing
    {R : Type*} [CommRing R] {M1 M2 M3 : Type*} (N : Type*)
    [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3] [AddCommGroup N]
    [Module R M1] [Module R M2] [Module R M3] [Module R N]
    {f : M1 →ₗ[R] M2} {g : M2 →ₗ[R] M3}
    (exac : Function.Exact f g) (surj : Function.Surjective g) :
    Function.Exact (LinearMap.lcomp R N g) (LinearMap.lcomp R N f) := by
  simpa only [LinearMap.lcomp] using
    (exact_lcompₛₗ_of_exact_of_surjective
      (R₂ := R) (S := R) (N := N) (RingHom.id R) exac surj)

end LinearMap
