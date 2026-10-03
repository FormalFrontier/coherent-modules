/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

public import CoherentModules
public import Mathlib.Data.ZMod.Basic

/-!
External-use checks for universally coherent commutative rings.
-/

namespace CoherentModulesTest.UniversallyCoherent

universe u v w

section

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FinitePresentation R A]

private theorem finitelyPresentedAlgebra [IsUniversallyCoherent.{u, v} R] : IsCoherentRing A :=
  IsUniversallyCoherent.isCoherentRing R A

private theorem noetherianAlgebra [IsNoetherianRing R] : IsCoherentRing A :=
  IsUniversallyCoherent.isCoherentRing R A

private theorem baseRingCoherent [IsUniversallyCoherent.{u, u} R] :
    IsCoherentRing R := inferInstance

private theorem equivalentAlgebra (B : Type w) [CommRing B] [Algebra R B]
    [IsUniversallyCoherent.{u, w} R]
    (e : A ≃ₐ[R] B) : IsCoherentRing B :=
  IsUniversallyCoherent.isCoherentRing_of_algEquiv R e

end

private theorem integerHigherUniverse : IsUniversallyCoherent.{0, 1} ℤ := inferInstance

/-- The zero ring remains universally coherent in a higher algebra universe. -/
public theorem zeroRingHigherUniverse : IsUniversallyCoherent.{0, 1} (ZMod 1) := inferInstance

private theorem integerPolynomial : IsCoherentRing (Polynomial ℤ) :=
  IsUniversallyCoherent.isCoherentRing ℤ (Polynomial ℤ)

-- Selected named-client axiom checks, not a complete release census.
#print axioms finitelyPresentedAlgebra
#print axioms noetherianAlgebra
#print axioms baseRingCoherent
#print axioms equivalentAlgebra
#print axioms integerHigherUniverse
#print axioms zeroRingHigherUniverse
#print axioms integerPolynomial

end CoherentModulesTest.UniversallyCoherent
