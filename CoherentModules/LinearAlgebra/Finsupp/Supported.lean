/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.NoZeroSMulDivisors.Pi
public import CoherentModules.LinearAlgebra.Span.Kernel
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Pi

/-!
# Coordinate faces of spans

The submodule `Finsupp.supported A R J` is the kernel of the family of evaluations
outside `J`. If addition in the coefficient module is conical and its given
scalar action has no zero scalar divisors, intersecting an arbitrary span with
this submodule selects the generators supported in `J`. In particular, these
intersections preserve finite generation.

The index and support sets are arbitrary, including an empty complement. The
regular-coefficient corollaries use the usual left action of the semiring on itself.
-/

@[expose] public section

universe uR uA uI

namespace Finsupp

variable {R : Type uR} {A : Type uA} {I : Type uI}
variable [Semiring R] [AddCommMonoid A] [Module R A]

/-- The family of evaluations outside a support set has precisely the supported
submodule as its kernel. -/
theorem ker_pi_lapply_compl (J : Set I) :
    LinearMap.ker (LinearMap.pi (fun i : {i : I // i ∉ J} =>
      (Finsupp.lapply i.1 : (I →₀ A) →ₗ[R] A))) = supported A R J := by
  ext p
  rw [LinearMap.mem_ker, mem_supported']
  constructor
  · intro h i hi
    simpa only [LinearMap.pi_apply, lapply_apply, Pi.zero_apply] using congrFun h ⟨i, hi⟩
  · intro h
    funext i
    simpa only [LinearMap.pi_apply, lapply_apply, Pi.zero_apply] using h i.1 i.2

/-- Over a conical coefficient module with no zero scalar divisors, intersecting
a span with a coordinate face selects exactly the generators in that face. -/
theorem span_inf_supported_eq_span_inter [NoZeroSMulDivisors R A]
    (J : Set I) (S : Set (I →₀ A))
    (hA : ∀ ⦃a b : A⦄, a + b = 0 → a = 0 ∧ b = 0) :
    Submodule.span R S ⊓ supported A R J =
      Submodule.span R (S ∩ (supported A R J : Set (I →₀ A))) := by
  let _ : NoZeroSMulDivisors R ({i : I // i ∉ J} → A) :=
    Pi.noZeroSMulDivisors_of_components (R := R) (A := fun _ : {i : I // i ∉ J} => A)
  simpa only [ker_pi_lapply_compl] using
    Submodule.span_inf_ker_eq_span_inter
      (LinearMap.pi (fun i : {i : I // i ∉ J} =>
        (Finsupp.lapply i.1 : (I →₀ A) →ₗ[R] A))) S
      (by
        intro p q h
        exact Pi.eq_zero_and_eq_zero_of_add_eq_zero (fun _ => hA) h)

/-- For regular coefficients, conical addition and absence of zero divisors in
the semiring suffice for the coordinate-face span formula. -/
theorem span_inf_supported_eq_span_inter_self [NoZeroDivisors R]
    (J : Set I) (S : Set (I →₀ R))
    (hR : ∀ ⦃a b : R⦄, a + b = 0 → a = 0 ∧ b = 0) :
    Submodule.span R S ⊓ supported R R J =
      Submodule.span R (S ∩ (supported R R J : Set (I →₀ R))) :=
  span_inf_supported_eq_span_inter J S hR

end Finsupp

namespace Submodule

variable {R : Type uR} {A : Type uA} {I : Type uI}
variable [Semiring R] [AddCommMonoid A] [Module R A]

/-- Coordinate-face intersections of finitely generated submodules remain
finitely generated for conical coefficients with no zero scalar divisors. -/
theorem FG.inf_supported [NoZeroSMulDivisors R A] (J : Set I)
    {K : Submodule R (I →₀ A)} (hK : K.FG)
    (hA : ∀ ⦃a b : A⦄, a + b = 0 → a = 0 ∧ b = 0) :
    (K ⊓ Finsupp.supported A R J).FG := by
  let _ : NoZeroSMulDivisors R ({i : I // i ∉ J} → A) :=
    Pi.noZeroSMulDivisors_of_components (R := R) (A := fun _ : {i : I // i ∉ J} => A)
  simpa only [Finsupp.ker_pi_lapply_compl] using
    hK.inf_ker (LinearMap.pi (fun i : {i : I // i ∉ J} =>
      (Finsupp.lapply i.1 : (I →₀ A) →ₗ[R] A)))
      (by
        intro p q h
        exact Pi.eq_zero_and_eq_zero_of_add_eq_zero (fun _ => hA) h)

/-- Over a conical semiring without zero divisors, coordinate-face intersections
of finitely generated submodules of its regular Finsupp module are finitely generated. -/
theorem FG.inf_supported_self [NoZeroDivisors R] (J : Set I)
    {K : Submodule R (I →₀ R)} (hK : K.FG)
    (hR : ∀ ⦃a b : R⦄, a + b = 0 → a = 0 ∧ b = 0) :
    (K ⊓ Finsupp.supported R R J).FG :=
  FG.inf_supported J hK hR

end Submodule
