/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Morita.Matrix

/-!
# Matrix-semimodule equivalence over the natural numbers

The categorical unit embeds a nonzero coefficient as a nonzero supported vector. This
uses a semiring and an additive monoid without additive inverses.
-/

@[expose] public section

open CategoryTheory
open scoped Matrix.Module

example :
    (SemimoduleCat.matrixEquivalence ℕ (0 : Fin 2)).unitIso.hom.app
      (SemimoduleCat.of ℕ ℕ) (1 : ℕ) ≠ 0 := by
  intro h
  let e := (SemimoduleCat.matrixEquivalence ℕ (0 : Fin 2)).unitIso.app
    (SemimoduleCat.of ℕ ℕ)
  have h' := congrArg e.inv.hom h
  have h1 : (1 : ℕ) = 0 :=
    (SemimoduleCat.inv_hom_apply e (1 : ℕ)).symm.trans (h'.trans (map_zero e.inv.hom))
  exact Nat.one_ne_zero h1

example (x : Fin 2 → ℕ) :
    (SemimoduleCat.matrixEquivalence ℕ (0 : Fin 2)).counitIso.hom.app
        ((SemimoduleCat.toMatrixModCat ℕ (Fin 2)).obj (SemimoduleCat.of ℕ ℕ))
        ((SemimoduleCat.toMatrixModCat ℕ (Fin 2)).map
          ((SemimoduleCat.matrixEquivalence ℕ (0 : Fin 2)).unitIso.hom.app
            (SemimoduleCat.of ℕ ℕ)) x) = x := by
  exact DFunLike.congr_fun
    (congrArg SemimoduleCat.Hom.hom
      ((SemimoduleCat.matrixEquivalence ℕ (0 : Fin 2)).functor_unitIso_comp
        (SemimoduleCat.of ℕ ℕ))) x
