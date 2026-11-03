/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.LinearAlgebra.LinearMap.Evaluation

/-!
# Power covariance and regular representations

Polynomial intertwining recovers power covariance under the hypotheses of
`Module.End.commute_pow_left_of_commute`. For regular left-multiplication representations,
evaluation at `1` recovers the relation of `Polynomial.hom_eval₂`.
-/

universe uR uR₂ uS uA uB uM uN

/-- Natural-number coefficients and a power of `X` recover semilinear power covariance,
without any additional scalar actions on the semilinear Hom. -/
private theorem pow_comp_of_intertwining
    {R : Type uR} {R₂ : Type uR₂} [Semiring R] [Semiring R₂]
    {M : Type uM} {N : Type uN} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R₂ N] {η : R →+* R₂}
    (h : M →ₛₗ[η] N) (f : Module.End R M) (g : Module.End R₂ N)
    (hfg : g.comp h = h.comp f) (n : ℕ) :
    (g ^ n).comp h = h.comp (f ^ n) := by
  simpa only [Polynomial.eval₂_X_pow] using
    LinearMap.eval₂_comp h (Nat.castRingHom (Module.End R M))
      (Nat.castRingHom (Module.End R₂ N)) f g
      (fun k ↦ by ext m; simp) hfg (Polynomial.X ^ n : Polynomial ℕ)

/-- Applying additive polynomial intertwining to regular left-multiplication representations
and evaluating at `1` recovers ordinary evaluation transport over arbitrary semirings. -/
private theorem hom_eval₂_leftRegular
    {S : Type uS} {A : Type uA} {B : Type uB}
    [Semiring S] [Semiring A] [Semiring B]
    (c : S →+* A) (k : A →+* B) (p : Polynomial S) (x : A) :
    k (p.eval₂ c x) = p.eval₂ (k.comp c) (k x) := by
  let Lₐ := Module.toAddMonoidEnd A A
  let Lᵦ := Module.toAddMonoidEnd B B
  have heval := Polynomial.semiconj_eval₂ k.toAddMonoidHom
    (Lₐ.comp c) (Lᵦ.comp (k.comp c)) (Lₐ x) (Lᵦ (k x))
    (fun s a ↦ k.map_mul (c s) a) (fun a ↦ k.map_mul x a) p
  have hone := heval 1
  rw [← Polynomial.hom_eval₂ p c Lₐ x,
    ← Polynomial.hom_eval₂ p (k.comp c) Lᵦ (k x)] at hone
  have hmul : k (p.eval₂ c x * 1) = p.eval₂ (k.comp c) (k x) * k 1 := hone
  simpa only [map_one, mul_one] using hmul
