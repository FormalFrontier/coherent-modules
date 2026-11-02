/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Ideal.Operations

/-!
# Relative generation modulo a sum of nilpotent left ideals

Global nilpotence of two left ideals lets their sum be removed from a relative
generation bound. The coefficient semiring and semimodule have independent
universes; neither commutativity nor finite generation is required.
-/

universe u v

open scoped Pointwise

namespace Submodule

example {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
    (I J : Ideal R) (N P : Submodule R M)
    (hI : IsNilpotent I) (hJ : IsNilpotent J) (h : P ≤ N ⊔ (I ⊔ J) • P) :
    P ≤ N :=
  le_of_le_sup_smul_of_isNilpotent (Ideal.isNilpotent_sup hI hJ) h

end Submodule
