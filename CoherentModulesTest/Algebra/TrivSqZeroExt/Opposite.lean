/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.TrivSqZeroExt.Coherent
import CoherentModules.Algebra.TrivSqZeroExt.Opposite
import Mathlib.Algebra.Field.Opposite

/-!
# Right coherence through the opposite equivalence

The opposite equivalence swaps the given bimodule actions. This example combines it
with the division-ring left-coherence criterion and coherence transport, using Mathlib's
module pullback for the double-opposite action. Finiteness is measured using the original
right action, without identifying left and right finite generation.
-/

universe uD uM

example (D : Type uD) (M : Type uM)
    [DivisionRing D] [AddCommGroup M] [Module D M] [Module Dᵐᵒᵖ M]
    [SMulCommClass D Dᵐᵒᵖ M] :
    IsCoherentRing ((TrivSqZeroExt D M)ᵐᵒᵖ) ↔ Module.Finite Dᵐᵒᵖ M := by
  let _ : Module Dᵐᵒᵖᵐᵒᵖ M :=
    Module.compHom M (RingEquiv.opOp D).symm.toRingHom
  let _ : SMulCommClass Dᵐᵒᵖᵐᵒᵖ Dᵐᵒᵖ M :=
    SMul.comp.smulCommClass
      ((RingEquiv.opOp D).symm.toRingHom : Dᵐᵒᵖᵐᵒᵖ → D)
  let _ : SMulCommClass Dᵐᵒᵖ Dᵐᵒᵖᵐᵒᵖ M :=
    SMulCommClass.symm _ _ _
  let e : (TrivSqZeroExt D M)ᵐᵒᵖ ≃+* TrivSqZeroExt Dᵐᵒᵖ M :=
    TrivSqZeroExt.opEquiv (R := D) (M := M)
  constructor
  · intro h
    let _ : IsCoherentRing ((TrivSqZeroExt D M)ᵐᵒᵖ) := h
    exact (TrivSqZeroExt.isCoherentRing_iff_finite_of_divisionRing Dᵐᵒᵖ M).mp
      (IsCoherentRing.of_ringEquiv e)
  · intro h
    let _ : IsCoherentRing (TrivSqZeroExt Dᵐᵒᵖ M) :=
      (TrivSqZeroExt.isCoherentRing_iff_finite_of_divisionRing Dᵐᵒᵖ M).mpr h
    exact IsCoherentRing.of_ringEquiv e.symm
