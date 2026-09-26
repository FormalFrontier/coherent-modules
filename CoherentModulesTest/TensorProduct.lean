/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

import CoherentModules.TensorProduct

/-!
# Tensor-product public-use examples
-/

open scoped TensorProduct

namespace CoherentModulesTest.TensorProduct

universe u v w

private theorem tensorCoherent (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M ⊗[R] N) :=
  Module.IsCoherent.tensorProduct

private theorem integerTensor : Module.IsCoherent ℤ (ℤ ⊗[ℤ] ℤ) :=
  Module.IsCoherent.tensorProduct

private theorem zeroRingIndependentUniverses : Module.IsCoherent (ZMod 1) (PUnit.{1} ⊗[ZMod 1] PUnit.{2}) :=
  Module.IsCoherent.tensorProduct

private theorem rankZeroTensor (R : Type u) [CommRing R]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.IsCoherent R N] :
    Module.IsCoherent R ((Fin 0 → R) ⊗[R] N) :=
  Module.IsCoherent.tensorProduct

private theorem emptyIndexTensor (R : Type u) [CommRing R]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.IsCoherent R N] :
    Module.IsCoherent R ((Empty → R) ⊗[R] N) :=
  Module.IsCoherent.tensorProduct

-- Selected named-client axiom checks, not a complete release census.
#print axioms tensorCoherent
#print axioms integerTensor
#print axioms zeroRingIndependentUniverses
#print axioms rankZeroTensor
#print axioms emptyIndexTensor

end CoherentModulesTest.TensorProduct
