/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Module

/-!
# Additive Hom and endomorphism equivalences for matrix columns

For a finite type `I`, matrices act on `I → M` by
`(A • v) i = ∑ j, A i j • v j`, with the given `Module R M`.
Coordinatewise extension `LinearMap.matrixModuleMap` is surjective even when
`I` is empty. A matrix-linear map is determined by its diagonal coordinate restrictions.

For nonempty `I`, `LinearMap.matrixModuleHomAddEquiv` is an additive equivalence
between the coefficient Hom and the matrix-linear Hom of columns. Its inverse can
be evaluated at any coordinate. `Module.matrixModuleEndRingEquiv` is the induced
endomorphism semiring equivalence, with multiplication given by composition in
its usual order. In particular, for the regular coefficient module the endomorphisms
of columns form `Rᵐᵒᵖ`, not the full matrix semiring.

The coefficient semiring may be noncommutative or zero. All modules retain their
given coefficient actions; no scalar-module structure on a general Hom is used.
The column action is available in the scope `Matrix.Module`.

## References

The action and coordinate extension follow Yunzhou Xie's formalization in
`Mathlib.LinearAlgebra.Matrix.Module`. The ring case of Hom bijectivity is also
contained in `ModuleCat.matrixEquivalence` in `Mathlib.RingTheory.Morita.Matrix`.
-/

@[expose] public section

universe uR uI uM uN

variable {R : Type uR} {I : Type uI} {M : Type uM} {N : Type uN}

open scoped Matrix.Module

namespace LinearMap

variable [Semiring R] [Fintype I] [DecidableEq I]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Commuting with a diagonal matrix unit isolates the corresponding coordinate. -/
private theorem matrixModuleHom_apply_eq_single
    (g : (I → M) →ₗ[Matrix I I R] (I → N)) (v : I → M) (i : I) :
    g v i = g (Pi.single i (v i)) i := by
  have h := congrFun (g.map_smul (Matrix.single i i (1 : R)) v) i
  simpa only [Matrix.Module.single_smul_semiring, one_smul, Pi.single_eq_same] using h.symm

/-- Off-diagonal matrix units identify the diagonal coordinate restrictions. -/
private theorem matrixModuleHom_single_coordinate
    (g : (I → M) →ₗ[Matrix I I R] (I → N)) (i j : I) (x : M) :
    g (Pi.single i x) i = g (Pi.single j x) j := by
  have h := congrFun (g.map_smul (Matrix.single j i (1 : R)) (Pi.single i x)) j
  simpa only [Matrix.Module.single_smul_semiring, one_smul, Pi.single_eq_same] using h.symm

/-- Each diagonal coordinate restriction is linear for the original coefficient action. -/
private def matrixModuleHomCoordinate
    (g : (I → M) →ₗ[Matrix I I R] (I → N)) (i : I) : M →ₗ[R] N where
  toFun x := g (Pi.single i x) i
  map_add' x y := by simp only [Pi.single_add, map_add, Pi.add_apply]
  map_smul' r x := by
    have h := congrFun (g.map_smul (Matrix.single i i r) (Pi.single i x)) i
    simpa only [Matrix.Module.single_smul_semiring, Pi.single_eq_same, RingHom.id_apply] using h

/-- A matrix-linear map of columns is determined by its diagonal coordinate restrictions. -/
theorem matrixModuleHom_ext (f g : (I → M) →ₗ[Matrix I I R] (I → N))
    (h : ∀ (i : I) (x : M), f (Pi.single i x) i = g (Pi.single i x) i) : f = g := by
  apply LinearMap.ext
  intro v
  funext i
  rw [matrixModuleHom_apply_eq_single f v i, matrixModuleHom_apply_eq_single g v i]
  exact h i (v i)

variable (I) in
/-- Coordinate extension is surjective even when the finite index is empty. -/
theorem matrixModuleMap_surjective :
    Function.Surjective (matrixModuleMap I (R := R) (M := M) (N := N)) := by
  classical
  intro g
  rcases isEmpty_or_nonempty I with hI | hI
  · exact ⟨0, Subsingleton.elim _ _⟩
  · let i : I := Classical.choice hI
    refine ⟨matrixModuleHomCoordinate g i, ?_⟩
    apply matrixModuleHom_ext
    intro j x
    change g (Pi.single i ((Pi.single j x : I → M) j)) i = g (Pi.single j x) j
    simpa only [Pi.single_eq_same] using matrixModuleHom_single_coordinate g i j x

variable (I) in
/-- For nonempty finite indices, coordinate extension is an additive equivalence.
Its inverse is characterized at every coordinate. -/
noncomputable def matrixModuleHomAddEquiv [Nonempty I] :
    (M →ₗ[R] N) ≃+ ((I → M) →ₗ[Matrix I I R] (I → N)) :=
  AddEquiv.ofBijective (matrixModuleMap I) ⟨by
    intro f g h
    apply LinearMap.ext
    intro x
    exact congrFun (LinearMap.congr_fun h (fun _ : I => x)) (Classical.choice ‹Nonempty I›),
    matrixModuleMap_surjective I⟩

/-- The Hom equivalence extends maps coordinatewise. -/
@[simp]
theorem matrixModuleHomAddEquiv_apply [Nonempty I] (f : M →ₗ[R] N) (v : I → M) (i : I) :
    matrixModuleHomAddEquiv I f v i = f (v i) :=
  matrixModuleMap_apply I f v i

/-- The inverse can be evaluated at any coordinate, not just an internal chosen one. -/
theorem matrixModuleHomAddEquiv_symm_apply [Nonempty I]
    (g : (I → M) →ₗ[Matrix I I R] (I → N)) (i : I) (x : M) :
    (matrixModuleHomAddEquiv I).symm g x = g (Pi.single i x) i := by
  have h := congrFun
    (LinearMap.congr_fun ((matrixModuleHomAddEquiv I).apply_symm_apply g) (Pi.single i x)) i
  simpa only [matrixModuleHomAddEquiv_apply, Pi.single_eq_same] using h

/-- Every coordinate of a matrix-linear column map is given by its inverse Hom image. -/
theorem matrixModuleHom_apply [Nonempty I]
    (g : (I → M) →ₗ[Matrix I I R] (I → N)) (v : I → M) (i : I) :
    g v i = (matrixModuleHomAddEquiv I).symm g (v i) := by
  rw [matrixModuleHomAddEquiv_symm_apply]
  exact matrixModuleHom_apply_eq_single g v i

end LinearMap

namespace Module

variable [Semiring R] [Fintype I] [DecidableEq I] [AddCommMonoid M] [Module R M]

variable (I) in
/-- The endomorphism semiring equivalence induced by coordinate extension.
Multiplication on both sides is composition in the same order. -/
noncomputable def matrixModuleEndRingEquiv [Nonempty I] :
    Module.End R M ≃+* Module.End (Matrix I I R) (I → M) where
  __ := LinearMap.matrixModuleHomAddEquiv I
  map_mul' f g := by
    exact LinearMap.matrixModuleMap_comp I g f

/-- The End equivalence has exactly the same forward map as the Hom extension. -/
@[simp]
theorem matrixModuleEndRingEquiv_apply [Nonempty I] (f : Module.End R M) :
    matrixModuleEndRingEquiv I f = LinearMap.matrixModuleMap I f := rfl

/-- The inverse End equivalence can be evaluated at any coordinate. -/
theorem matrixModuleEndRingEquiv_symm_apply [Nonempty I]
    (g : Module.End (Matrix I I R) (I → M)) (i : I) (x : M) :
    (matrixModuleEndRingEquiv I).symm g x = g (Pi.single i x) i :=
  LinearMap.matrixModuleHomAddEquiv_symm_apply g i x

end Module
