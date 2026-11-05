/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.NoZeroSMulDivisors.Pi
public import CoherentModules.LinearAlgebra.Polynomial.Span
public import CoherentModules.LinearAlgebra.Polynomial.Supported
public import CoherentModules.LinearAlgebra.Span.Kernel
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite generation of bounded polynomial coefficient faces

Let `K` be a finitely generated submodule of a free left polynomial module over
an arbitrary zero-sum-free semiring without zero divisors. Restricting scalars
to the coefficient semiring and requiring coefficients outside a degree-bounded
set of coordinates to vanish gives a finitely generated submodule.

Neither the coordinate type nor the set of allowed coefficient coordinates
needs to be finite. All scalar actions are the original pointwise left actions;
in particular, the coefficient semiring need not be commutative.
-/

@[expose] public section

universe u v

namespace Polynomial

variable {R : Type u} {I : Type v} [Semiring R] [NoZeroDivisors R]

/-- A degree-bounded coefficient face of a finitely generated submodule of a free
left polynomial module is finitely generated over the coefficient semiring.
The allowed coordinates may correlate the module index with the degree. -/
theorem fg_restrictScalars_coefficient_face
    (hR : ∀ a b : R, a + b = 0 → a = 0 ∧ b = 0)
    (K : Submodule R[X] (I →₀ R[X])) (hK : K.FG)
    (J : Set (I × ℕ)) (D : ℕ) (hJ : ∀ p ∈ J, p.2 ≤ D) :
    ((K.restrictScalars R) ⊓
      (⨅ p : {p : I × ℕ // p ∉ J},
        LinearMap.ker ((lcoeff R p.1.2).comp
          (Finsupp.lapply (R := R) p.1.1)))).FG := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  have hspan : K.restrictScalars R =
      Submodule.span R
        (Set.range (fun p : Fin n × ℕ => (X ^ p.2 : R[X]) • g p.1)) := by
    rw [← hg, restrictScalars_span_range]
  let q : (I →₀ R[X]) →ₗ[R] ({p : I × ℕ // p ∉ J} → R) :=
    LinearMap.pi fun p =>
      (lcoeff R p.1.2).comp (Finsupp.lapply (R := R) p.1.1)
  have hq : q.ker =
      ⨅ p : {p : I × ℕ // p ∉ J},
        LinearMap.ker ((lcoeff R p.1.2).comp
          (Finsupp.lapply (R := R) p.1.1)) :=
    LinearMap.ker_pi _
  have hq_coe : (q.ker : Set (I →₀ R[X])) =
      {v | ∀ p ∉ J, (v p.1).coeff p.2 = 0} := by
    ext v
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · intro hv p hp
      simpa only [q, LinearMap.pi_apply, LinearMap.comp_apply,
        lcoeff_apply, Finsupp.lapply_apply, Pi.zero_apply] using
        congrFun hv (⟨p, hp⟩ : {p : I × ℕ // p ∉ J})
    · intro hv
      funext p
      simpa only [q, LinearMap.pi_apply, LinearMap.comp_apply,
        lcoeff_apply, Finsupp.lapply_apply, Pi.zero_apply] using hv p.1 p.2
  let _ : NoZeroSMulDivisors R ({p : I × ℕ // p ∉ J} → R) :=
    Pi.noZeroSMulDivisors_of_components
      (R := R) (A := fun _ : {p : I × ℕ // p ∉ J} => R)
  have hN : ∀ ⦃a b : {p : I × ℕ // p ∉ J} → R⦄,
      a + b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    exact Pi.eq_zero_and_eq_zero_of_add_eq_zero (fun _ {r s} h => hR r s h) hab
  rw [← hq, hspan, Submodule.span_inf_ker_eq_span_inter q _ hN]
  apply Submodule.fg_def.mpr
  refine ⟨_, ?_, rfl⟩
  rw [hq_coe]
  exact finite_range_X_pow_smul_inter g hJ

end Polynomial
