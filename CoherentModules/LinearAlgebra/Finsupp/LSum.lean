/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Pi

/-!
# Semilinear maps from free semimodules

`Finsupp.lliftₛₗ` identifies families of elements of `N` with semilinear maps from the free
`R`-semimodule, for any homomorphism `σ : R →+* R₂`. The equivalence is linear over a semiring
`S` whose given action on `N` commutes with the given `R₂`-action. The index type is arbitrary,
and the scalar, module and index universes are independent.

The characteristic formulas give evaluation on every single coefficient and on unit generators.
`Finsupp.eq_lliftₛₗ_iff` is the universal property, and `Finsupp.lliftₛₗ_id` identifies the
identity-semilinearity specialization with `Finsupp.llift`, with the same module structures.

## Implementation notes

The construction composes Mathlib's regular-module equivalence and semilinear precomposition,
then uses `LinearMap.piMap` and the already semilinear `Finsupp.lsum`. Evaluation at `1` is an
application of `LinearMap.flip` to the identity map. No `R`-module structure on `N` is needed.

## References and credit

This generalizes Mathlib's `Finsupp.llift` using its `Finsupp.lsum` formalization by Johannes
Hölzl, together with Mathlib's regular-module and product-map APIs and the bilinear-map
formalization by Kenny Lau and Mario Carneiro.
-/

@[expose] public section

noncomputable section

universe uR uR₂ uS uN uι

namespace Finsupp

section Semilinear

variable {N : Type uN} {R : Type uR} {R₂ : Type uR₂} {S : Type uS} {ι : Type uι}
variable [Semiring R] [Semiring R₂] [Semiring S] [AddCommMonoid N]
variable [Module R₂ N] [Module S N] [SMulCommClass R₂ S N]
variable (σ : R →+* R₂)

private def lliftCoeff : N →ₗ[S] (R →ₛₗ[σ] N) :=
  (LinearMap.lcompₛₗ (σ₁₃ := σ) S N (RingHom.id R₂) σ.toSemilinearMap).comp
    (LinearMap.ringLmapEquivSelf R₂ S N).symm.toLinearMap

private theorem lliftCoeff_apply (n : N) (r : R) :
    lliftCoeff (S := S) σ n r = σ r • n :=
  rfl

private def lliftEval : (R →ₛₗ[σ] N) →ₗ[S] N :=
  LinearMap.flip (LinearMap.id (R := S) (M := R →ₛₗ[σ] N)) (1 : R)

private theorem lliftEval_apply (f : R →ₛₗ[σ] N) : lliftEval (S := S) σ f = f 1 :=
  rfl

private theorem lliftEval_coeff (n : N) :
    lliftEval (S := S) σ (lliftCoeff (S := S) σ n) = n := by
  simp only [lliftEval_apply, lliftCoeff_apply, map_one, one_smul]

private theorem lliftCoeff_eval (f : R →ₛₗ[σ] N) :
    lliftCoeff (S := S) σ (lliftEval (S := S) σ f) = f := by
  apply LinearMap.ext_ring
  simp only [lliftCoeff_apply, lliftEval_apply, map_one, one_smul]

private def lliftForward : (ι → N) →ₗ[S] ((ι →₀ R) →ₛₗ[σ] N) :=
  (lsum (α := ι) (M := R) (N := N) (R := R) (R₂ := R₂) (σ := σ) S).toLinearMap.comp
    (LinearMap.piMap (fun _ : ι => lliftCoeff (S := S) (N := N) σ))

private def lliftBackward : ((ι →₀ R) →ₛₗ[σ] N) →ₗ[S] (ι → N) :=
  (LinearMap.piMap (fun _ : ι => lliftEval (S := S) (N := N) σ)).comp
    (lsum (α := ι) (M := R) (N := N) (R := R) (R₂ := R₂) (σ := σ) S).symm.toLinearMap

private theorem lliftForward_eq_lsum (a : ι → N) :
    lliftForward (S := S) σ a = lsum S (fun i => lliftCoeff (S := S) σ (a i)) :=
  rfl

private theorem lliftForward_apply (a : ι → N) (d : ι →₀ R) :
    lliftForward (S := S) σ a d = d.sum (fun i r => σ r • a i) := by
  rw [lliftForward_eq_lsum, lsum_apply]
  rfl

private theorem lliftForward_single (a : ι → N) (i : ι) (r : R) :
    lliftForward (S := S) σ a (single i r) = σ r • a i := by
  rw [lliftForward_eq_lsum, lsum_single, lliftCoeff_apply]

private theorem lliftBackward_apply (f : (ι →₀ R) →ₛₗ[σ] N) (i : ι) :
    lliftBackward (S := S) σ f i = lliftEval (S := S) σ ((lsum S).symm f i) :=
  rfl

private theorem lliftBackward_apply_single (f : (ι →₀ R) →ₛₗ[σ] N) (i : ι) :
    lliftBackward (S := S) σ f i = f (single i 1) := by
  rw [lliftBackward_apply, lsum_symm_apply, lliftEval_apply, LinearMap.comp_apply,
    lsingle_apply]

private theorem lliftForward_comp_backward :
    (lliftForward (S := S) (N := N) (ι := ι) σ).comp (lliftBackward (S := S) σ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply (lsum (α := ι) (M := R) (N := N) (σ := σ) S).symm.injective
  rw [LinearMap.comp_apply, LinearMap.id_apply, lliftForward_eq_lsum,
    LinearEquiv.symm_apply_apply]
  funext i
  exact lliftCoeff_eval (S := S) σ ((lsum S).symm f i)

private theorem lliftBackward_comp_forward :
    (lliftBackward (S := S) (N := N) (ι := ι) σ).comp (lliftForward (S := S) σ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext i
  rw [LinearMap.comp_apply, LinearMap.id_apply, lliftBackward_apply, lliftForward_eq_lsum,
    LinearEquiv.symm_apply_apply]
  exact lliftEval_coeff (S := S) σ (a i)

variable (N R S ι) in
/-- Families in an `R₂`-semimodule are `S`-linearly equivalent to `σ`-semilinear maps from the
free `R`-semimodule, when the given `R₂`- and `S`-actions commute.

This generalizes `Finsupp.llift` to an arbitrary homomorphism `σ : R →+* R₂`, without an
`R`-action on the target or a finiteness assumption on the index type. -/
def lliftₛₗ : (ι → N) ≃ₗ[S] ((ι →₀ R) →ₛₗ[σ] N) :=
  -- Elaborate the body privately without making the implementation helpers public.
  private_decl%
    (LinearEquiv.ofLinearMap (lliftForward (S := S) σ) (lliftBackward (S := S) σ)
      (lliftForward_comp_backward σ) (lliftBackward_comp_forward σ))

/-- The semilinear extension is the finitely supported sum of the scaled generator values. -/
theorem lliftₛₗ_apply (a : ι → N) (d : ι →₀ R) :
    lliftₛₗ N R S ι σ a d = d.sum (fun i r => σ r • a i) :=
  lliftForward_apply (S := S) σ a d

/-- The support-sum formula for the semilinear extension of a family. -/
theorem lliftₛₗ_apply_eq_sum (a : ι → N) (d : ι →₀ R) :
    lliftₛₗ N R S ι σ a d = ∑ i ∈ d.support, σ (d i) • a i :=
  lliftₛₗ_apply (S := S) σ a d

/-- Evaluation of the semilinear extension at a generator with arbitrary coefficient. -/
@[simp]
theorem lliftₛₗ_single (a : ι → N) (i : ι) (r : R) :
    lliftₛₗ N R S ι σ a (single i r) = σ r • a i :=
  lliftForward_single (S := S) σ a i r

/-- The semilinear extension takes each unit generator to the prescribed value. -/
theorem lliftₛₗ_single_one (a : ι → N) (i : ι) :
    lliftₛₗ N R S ι σ a (single i 1) = a i := by
  simp only [lliftₛₗ_single, map_one, one_smul]

/-- The inverse equivalence records the values of a map on the unit generators. -/
@[simp]
theorem lliftₛₗ_symm_apply (f : (ι →₀ R) →ₛₗ[σ] N) (i : ι) :
    (lliftₛₗ N R S ι σ).symm f i = f (single i 1) :=
  lliftBackward_apply_single (S := S) σ f i

/-- Semilinear maps from a free semimodule are determined by their values on unit generators. -/
@[ext high]
theorem lhom_ext_single_one {f g : (ι →₀ R) →ₛₗ[σ] N}
    (h : ∀ i, f (single i 1) = g (single i 1)) : f = g := by
  apply lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simpa only [LinearMap.comp_apply, lsingle_apply] using h i

/-- The universal property of the free semimodule: a semilinear map is the extension of a
family exactly when it has that family's values on the unit generators. -/
theorem eq_lliftₛₗ_iff {a : ι → N} {f : (ι →₀ R) →ₛₗ[σ] N} :
    f = lliftₛₗ N R S ι σ a ↔ ∀ i, f (single i 1) = a i := by
  constructor
  · rintro rfl i
    exact lliftₛₗ_single_one (S := S) σ a i
  · intro h
    apply lhom_ext_single_one σ
    intro i
    rw [lliftₛₗ_single_one]
    exact h i

/-- Uniqueness of the semilinear extension with prescribed unit-generator values. -/
theorem lliftₛₗ_unique {a : ι → N} {f : (ι →₀ R) →ₛₗ[σ] N}
    (h : ∀ i, f (single i 1) = a i) : f = lliftₛₗ N R S ι σ a :=
  (eq_lliftₛₗ_iff (S := S) σ).2 h

end Semilinear

section Linear

variable {R : Type uR} {S : Type uS} {N : Type uN} {ι : Type uι}
variable [Semiring R] [Semiring S] [AddCommMonoid N]
variable [Module R N] [Module S N] [SMulCommClass R S N]

/-- At the identity homomorphism, the semilinear free-module equivalence is Mathlib's
`Finsupp.llift`, using the same given `R`- and `S`-module structures. -/
@[simp]
theorem lliftₛₗ_id : lliftₛₗ N R S ι (RingHom.id R) = llift N R S ι := by
  apply LinearEquiv.ext
  intro a
  apply (llift N R S ι).symm.injective
  calc
    (llift N R S ι).symm (lliftₛₗ N R S ι (RingHom.id R) a) = a := by
      funext i
      rw [llift_symm_apply, lliftₛₗ_single_one]
    _ = (llift N R S ι).symm (llift N R S ι a) :=
      ((llift N R S ι).symm_apply_apply a).symm

end Linear

end Finsupp
