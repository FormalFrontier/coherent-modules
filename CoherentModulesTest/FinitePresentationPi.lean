/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Pi
import Mathlib.Data.Matrix.Mul

/-!
# Finite presentation with varying coefficient rings and ranks

The product of a rank-two free integer module and a rank-three free module over
`Matrix (Fin 2) (Fin 2) ℤ` is finitely presented over the product coefficient ring.
The second ring is noncommutative, and both factors retain their regular scalar actions.
-/

private abbrev coefficientRing : Bool → Type
  | false => ℤ
  | true => Matrix (Fin 2) (Fin 2) ℤ

private instance : ∀ b, Ring (coefficientRing b) := fun b => by
  cases b <;> dsimp [coefficientRing] <;> infer_instance

private abbrev rank : Bool → ℕ
  | false => 2
  | true => 3

example : Module.FinitePresentation (∀ b, coefficientRing b)
    (∀ b, Fin (rank b) → coefficientRing b) := by
  apply (Module.FinitePresentation.piRing_iff coefficientRing
    (fun b => Fin (rank b) → coefficientRing b)).mpr
  intro b
  exact Module.finitePresentation_of_projective (coefficientRing b) _
