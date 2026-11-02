/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.LinearAlgebra.Projective.RestrictScalars

/-!
# Restriction of scalars through a product semiring
-/

example : Module.Projective ℕ ((ℕ × ℕ) × (ℕ × ℕ)) :=
  Module.Projective.restrictScalars
    (R := ℕ) (S := ℕ × ℕ) (M := (ℕ × ℕ) × (ℕ × ℕ))
