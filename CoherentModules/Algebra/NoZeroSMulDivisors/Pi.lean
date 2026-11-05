/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.NoZeroSMulDivisors.Pi

/-!
# Zero reflection in dependent products

Scalar multiplication on a dependent product reflects zero whenever it does so in
each component. Only the zero and scalar operations are needed. The comparison
lemmas identify this law with Mathlib's dependent and nondependent instances under
their semiring, domain and additive-group hypotheses, on the same pointwise action.

The additive zero-sum implication also lifts componentwise, independently of scalars.
-/

@[expose] public section

universe uR uI uA

namespace Pi

/-- A dependent product has no zero scalar divisors if each component has none.
The zero and scalar operations are the pointwise operations. -/
theorem noZeroSMulDivisors_of_components {R : Type uR} {I : Type uI} {A : I → Type uA}
    [Zero R] [∀ i, Zero (A i)] [∀ i, SMul R (A i)]
    [∀ i, NoZeroSMulDivisors R (A i)] : NoZeroSMulDivisors R (∀ i, A i) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    classical
    by_cases hc : c = 0
    · exact Or.inl hc
    · refine Or.inr (funext fun i => ?_)
      exact (eq_zero_or_eq_zero_of_smul_eq_zero (congrFun h i)).resolve_left hc

/-- The componentwise zero-reflection law agrees with Mathlib's dependent-product
instance when the latter's hypotheses hold. -/
theorem noZeroSMulDivisors_of_components_eq {R : Type uR} {I : Type uI}
    {A : I → Type uA} [Semiring R] [IsDomain R] [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [∀ i, NoZeroSMulDivisors R (A i)] :
    noZeroSMulDivisors_of_components (R := R) (A := A) =
      Pi.noZeroSMulDivisors R :=
  Subsingleton.elim _ _

/-- A pointwise sum can vanish only when both functions vanish, if this holds in
all components. The index type may be empty. -/
theorem eq_zero_and_eq_zero_of_add_eq_zero {I : Type uI} {A : I → Type uA}
    [∀ i, Zero (A i)] [∀ i, Add (A i)]
    (hA : ∀ i, ∀ ⦃a b : A i⦄, a + b = 0 → a = 0 ∧ b = 0)
    {p q : ∀ i, A i} (h : p + q = 0) : p = 0 ∧ q = 0 := by
  exact ⟨funext fun i => (hA i (congrFun h i)).1,
    funext fun i => (hA i (congrFun h i)).2⟩

end Pi

namespace Function

/-- The componentwise zero-reflection law agrees with Mathlib's function-space
instance under its semiring, domain and additive-group hypotheses. -/
theorem noZeroSMulDivisors_of_components_eq {R : Type uR} {I : Type uI} {A : Type uA}
    [Semiring R] [IsDomain R] [AddCommGroup A] [Module R A] [NoZeroSMulDivisors R A] :
    Pi.noZeroSMulDivisors_of_components (R := R) (A := fun _ : I => A) =
      Function.noZeroSMulDivisors (ι := I) (α := R) (β := A) :=
  Subsingleton.elim _ _

end Function
