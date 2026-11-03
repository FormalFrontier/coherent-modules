/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.Defs

/-!
# Coextension and pointwise linear maps

For an algebra `S` over a commutative ring `R`, `CoextendScalars.restrictEquiv`
identifies the restriction to `R` of coextension with `S →ₗ[R] M`, with its
pointwise `R`-module structure. It agrees on evaluation with Mathlib's
`CoextendScalars.equiv`, whose linearity instead uses the translation action of `S`.

The comparison retains the given algebra module on `S`. Scalar compatibility
follows from centrality of the image of `algebraMap R S`, rather than an
identification of module structures.
-/

@[expose] public section

universe uR uS w

namespace ModuleCat

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S]

/-- Restricting the regular module along the algebra map gives the given algebra action. -/
theorem restrictScalars.algebraMap_smul (r : R)
    (s : (restrictScalars (algebraMap R S)).obj (of S S)) :
    (show S from (r • s : (restrictScalars (algebraMap R S)).obj (of S S))) =
      r • (show S from s) := by
  have h : (show S from (r • s : (restrictScalars (algebraMap R S)).obj (of S S))) =
      algebraMap R S r * (show S from s) :=
    restrictScalars.smul_def (algebraMap R S) r s
  exact h.trans (Algebra.smul_def r (show S from s)).symm

namespace CoextendScalars

variable (M : ModuleCat.{w} R)

/-- Translation by a base scalar evaluates as pointwise scaling by that scalar. -/
theorem equiv_algebraMap_smul_apply (r : R)
    (ψ : (coextendScalars (algebraMap R S)).obj M) (s : S) :
    (equiv (algebraMap R S) M (algebraMap R S r • ψ)) s =
      r • (equiv (algebraMap R S) M ψ) s := by
  rw [map_smul, smul_apply', ← Algebra.commutes]
  have h := (equiv (algebraMap R S) M ψ).map_smul r
    (show (restrictScalars (algebraMap R S)).obj (of S S) from s)
  rw [restrictScalars.smul_def] at h
  exact h

/-- Coextension, restricted to the commutative base, is the pointwise linear Hom. -/
noncomputable def restrictEquiv :
    ((restrictScalars (algebraMap R S)).obj
      ((coextendScalars (algebraMap R S)).obj M)) ≃ₗ[R] (S →ₗ[R] M) := by
  let e : ((restrictScalars (algebraMap R S)).obj (of S S) →ₗ[R] M) ≃+ (S →ₗ[R] M) :=
    { toFun q :=
        { toFun := q
          map_add' := q.map_add
          map_smul' := by
            intro r s
            change q (r • s) = r • q s
            have h := restrictScalars.algebraMap_smul r
              (show (restrictScalars (algebraMap R S)).obj (of S S) from s)
            exact (congrArg q h.symm).trans (q.map_smul r _) }
      invFun q :=
        { toFun := q
          map_add' := q.map_add
          map_smul' := by
            intro r s
            change q (show S from (r • s)) = r • q s
            exact (congrArg q (restrictScalars.algebraMap_smul r s)).trans (q.map_smul r _) }
      left_inv q := by ext s; rfl
      right_inv q := by ext s; rfl
      map_add' q q' := by ext s; rfl }
  exact
    { toFun ψ := e (equiv (algebraMap R S) M ψ)
      invFun φ := (equiv (algebraMap R S) M).symm (e.symm φ)
      left_inv ψ := by
        exact (congrArg (equiv (algebraMap R S) M).symm
          (e.symm_apply_apply ((equiv (algebraMap R S) M) ψ))).trans
            ((equiv (algebraMap R S) M).symm_apply_apply ψ)
      right_inv φ := by
        exact (congrArg e ((equiv (algebraMap R S) M).apply_symm_apply (e.symm φ))).trans
          (e.apply_symm_apply φ)
      map_add' ψ χ := by
        exact (congrArg e ((equiv (algebraMap R S) M).map_add ψ χ)).trans
          (e.map_add _ _)
      map_smul' r ψ := by
        ext s
        change (equiv (algebraMap R S) M
          (r • ψ : (restrictScalars (algebraMap R S)).obj
            ((coextendScalars (algebraMap R S)).obj M))) s =
          r • (equiv (algebraMap R S) M ψ) s
        rw [restrictScalars.smul_def]
        exact equiv_algebraMap_smul_apply M r ψ s }

/-- The comparison with pointwise Hom agrees on evaluation with the coextension equivalence. -/
@[simp]
theorem restrictEquiv_apply
    (ψ : (restrictScalars (algebraMap R S)).obj
      ((coextendScalars (algebraMap R S)).obj M)) (s : S) :
    restrictEquiv M ψ s = (equiv (algebraMap R S) M ψ) s := rfl

/-- The inverse comparison agrees on evaluation with the coextension equivalence. -/
@[simp]
theorem equiv_restrictEquiv_symm_apply (φ : S →ₗ[R] M) (s : S) :
    (equiv (algebraMap R S) M ((restrictEquiv M).symm φ)) s = φ s := by
  exact (restrictEquiv_apply M _ s).symm.trans
    (congrArg (fun q : S →ₗ[R] M => q s) ((restrictEquiv M).apply_symm_apply φ))

/-- Coextension translation becomes precomposition by right multiplication. -/
theorem restrictEquiv_smul_apply
    (ψ : (coextendScalars (algebraMap R S)).obj M) (s t : S) :
    restrictEquiv M (s • ψ) t = restrictEquiv M ψ (t * s) := by
  change (equiv (algebraMap R S) M (s • ψ)) t =
    (equiv (algebraMap R S) M ψ) (t * s)
  rw [map_smul, smul_apply']

end CoextendScalars

end ModuleCat
