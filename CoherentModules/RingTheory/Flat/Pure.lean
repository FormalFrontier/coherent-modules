/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Flatness and pure scalar extension

Flatness descends along a scalar extension whose canonical tensor units are
injective. The test modules need only occupy the universe of the original
module and coefficient ring; the scalar algebra can have an independent universe.
The module may be an additive commutative monoid: its additive group structure
over a ring is derived internally.

The proof uses the equational criterion for flatness. After expanding the
factorization over the scalar algebra into finitely many pure tensors, both
sets of coefficient equations are encoded in one linear map. Injectivity of
the tensor unit on its cokernel descends their simultaneous solution.

## References

The proof uses Mathlib's equational criterion for flatness (Stacks Project,
Tags 00HK and 058D), finite tensor expansion, tensor products of finite products,
and the standard cokernel argument for pure scalar extension.
-/

@[expose] public section

universe uR uS uM

open scoped TensorProduct

namespace Module.Flat

/-- Expand the auxiliary tensors of a trivial relation without changing its
coefficient-annihilation identities. -/
private theorem exists_sum_tmul_coefficients
    {R : Type uR} {S : Type uS} {M : Type uM}
    [CommSemiring R] [CommRing S] [Algebra R S]
    [AddCommMonoid M] [Module R M]
    {l : ℕ} (a : Fin l → R) (m : Fin l → M)
    (h : Module.IsTrivialRelation (fun i => algebraMap R S (a i))
      (fun i => (1 : S) ⊗ₜ[R] m i)) :
    ∃ (k : ℕ) (b : Fin l → Fin k → S) (n : Fin k → M),
      (∀ i, (1 : S) ⊗ₜ[R] m i = ∑ j, b i j ⊗ₜ[R] n j) ∧
        ∀ j, ∑ i, algebraMap R S (a i) * b i j = 0 := by
  classical
  obtain ⟨k, d, z, hdz, hd⟩ := h
  -- Explicit finite witnesses are needed for the simultaneous coefficient equations;
  -- the stock expansion keeps every index in `Type 0`.
  choose q s n hn using fun j : Fin k => TensorProduct.exists_sum_tmul_eq (z j)
  let J : Type := Σ j : Fin k, Fin (q j)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let B (i : Fin l) (p : J) : S := d i p.1 * s p.1 p.2
  let n' (p : J) : M := n p.1 p.2
  refine ⟨Fintype.card J, (fun i t => B i (e.symm t)),
    (fun t => n' (e.symm t)), ?_, ?_⟩
  · intro i
    calc
      (1 : S) ⊗ₜ[R] m i = ∑ j, d i j • z j := hdz i
      _ = ∑ j, ∑ t, (d i j * s j t) ⊗ₜ[R] n j t := by
        simp_rw [hn, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul]
      _ = ∑ p : J, B i p ⊗ₜ[R] n' p := by
        simpa only [B, n', Finset.univ_sigma_univ] using
          (Finset.sum_sigma' Finset.univ
            (fun j : Fin k => (Finset.univ : Finset (Fin (q j))))
            (fun j t => (d i j * s j t) ⊗ₜ[R] n j t))
      _ = ∑ t : Fin (Fintype.card J), B i (e.symm t) ⊗ₜ[R] n' (e.symm t) :=
        (e.symm.sum_comp (fun p : J => B i p ⊗ₜ[R] n' p)).symm
  · intro t
    change (∑ i, algebraMap R S (a i) *
      (d i (e.symm t).1 * s (e.symm t).1 (e.symm t).2)) = 0
    simpa only [Finset.sum_mul, mul_assoc, zero_mul] using
      congrArg (fun c : S => c * s (e.symm t).1 (e.symm t).2) (hd (e.symm t).1)

private theorem isTrivialRelation_of_tensor_coefficients
    {R : Type uR} {M : Type uM} [CommRing R]
    [AddCommGroup M] [Module R M]
    {S : Type uS} [CommRing S] [Algebra R S]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1))
    {l k : ℕ} (a : Fin l → R) (m : Fin l → M)
    (b : Fin l → Fin k → S) (n : Fin k → M)
    (hb : ∀ i, (1 : S) ⊗ₜ[R] m i = ∑ j, b i j ⊗ₜ[R] n j)
    (hc : ∀ j, ∑ i, algebraMap R S (a i) * b i j = 0) :
    Module.IsTrivialRelation a m := by
  classical
  let D := Fin l × Fin k → R
  let T := (Fin l → M) × (Fin k → R)
  let L : D →ₗ[R] T :=
    (LinearMap.pi fun i => ∑ j,
      (LinearMap.toSpanSingleton R M (n j)).comp
        (LinearMap.proj (i, j) : D →ₗ[R] R)).prod
      (LinearMap.pi fun j => ∑ i, a i • (LinearMap.proj (i, j) : D →ₗ[R] R))
  have hL_apply (e : D) :
      L e = (fun i => ∑ j, e (i, j) • n j, fun j => ∑ i, a i * e (i, j)) := by
    apply Prod.ext
    · funext i
      change (∑ j, (LinearMap.toSpanSingleton R M (n j)).comp
        (LinearMap.proj (i, j) : D →ₗ[R] R)) e = _
      simp only [LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, LinearMap.proj_apply]
    · funext j
      change (∑ i, a i • (LinearMap.proj (i, j) : D →ₗ[R] R)) e = _
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul]
  let v : T := (m, 0)
  let w : S ⊗[R] D := ∑ i, ∑ j, b i j ⊗ₜ[R] Pi.single (i, j) 1
  have hL (i : Fin l) (j : Fin k) :
      L (Pi.single (i, j) 1) = (Pi.single i (n j), Pi.single j (a i)) := by
    apply Prod.ext
    · funext t
      by_cases ht : t = i
      · subst t
        simp [hL_apply, Pi.single_apply, Prod.mk.injEq, ite_smul]
      · simp [hL_apply, Pi.single_apply, Prod.mk.injEq, ht, ite_smul]
    · funext t
      by_cases ht : t = j
      · subst t
        simp [hL_apply, Pi.single_apply, Prod.mk.injEq, mul_ite]
      · simp [hL_apply, Pi.single_apply, Prod.mk.injEq, ht, mul_ite]
  have hw : L.lTensor S w = (1 : S) ⊗ₜ[R] v := by
    let E : S ⊗[R] T ≃ₗ[R] (Fin l → S ⊗[R] M) × (Fin k → S) :=
      (TensorProduct.prodRight R R S (Fin l → M) (Fin k → R)).trans
        ((TensorProduct.piRight R R S (fun _ : Fin l => M)).prodCongr
          (TensorProduct.piScalarRight R R S (Fin k)))
    have hE (s : S) (x : T) :
        E (s ⊗ₜ[R] x) = (fun i => s ⊗ₜ[R] x.1 i, fun j => x.2 j • s) := by
      rcases x with ⟨x₁, x₂⟩
      change ((TensorProduct.piRight R R S (fun _ : Fin l => M)).prodCongr
        (TensorProduct.piScalarRight R R S (Fin k)))
          ((TensorProduct.prodRight R R S (Fin l → M) (Fin k → R))
            (s ⊗ₜ[R] (x₁, x₂))) = _
      simp only [TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply,
        TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
        TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    let F (i : Fin l) : S ⊗[R] T →ₗ[R] S ⊗[R] M :=
      (LinearMap.proj i).comp
        ((LinearMap.fst R (Fin l → S ⊗[R] M) (Fin k → S)).comp E.toLinearMap)
    let G (j : Fin k) : S ⊗[R] T →ₗ[R] S :=
      (LinearMap.proj j).comp
        ((LinearMap.snd R (Fin l → S ⊗[R] M) (Fin k → S)).comp E.toLinearMap)
    have hF (i : Fin l) (s : S) (x : T) :
        F i (s ⊗ₜ[R] x) = s ⊗ₜ[R] x.1 i := by
      change (E (s ⊗ₜ[R] x)).1 i = _
      rw [hE]
    have hG (j : Fin k) (s : S) (x : T) :
        G j (s ⊗ₜ[R] x) = x.2 j • s := by
      change (E (s ⊗ₜ[R] x)).2 j = _
      rw [hE]
    apply E.injective
    apply Prod.ext
    · funext i
      change F i (L.lTensor S w) = F i ((1 : S) ⊗ₜ[R] v)
      simp only [w, map_sum, LinearMap.lTensor_tmul, hL, hF]
      simpa [v, Pi.single_apply, TensorProduct.tmul_ite] using (hb i).symm
    · funext j
      change G j (L.lTensor S w) = G j ((1 : S) ⊗ₜ[R] v)
      simp only [w, map_sum, LinearMap.lTensor_tmul, hL, hG]
      have hc' : ∑ i, a i • b i j = 0 := by
        simpa only [Algebra.smul_def] using hc j
      simpa [v, Pi.single_apply, ite_smul] using hc'
  let C := T ⧸ LinearMap.range L
  let q : T →ₗ[R] C := (LinearMap.range L).mkQ
  have hq : q v = 0 := by
    apply hunit C
    change (1 : S) ⊗ₜ[R] q v = (1 : S) ⊗ₜ[R] (0 : C)
    rw [TensorProduct.tmul_zero]
    calc
      (1 : S) ⊗ₜ[R] q v = q.lTensor S ((1 : S) ⊗ₜ[R] v) := rfl
      _ = q.lTensor S (L.lTensor S w) := congrArg (q.lTensor S) hw.symm
      _ = (q.comp L).lTensor S w := (LinearMap.lTensor_comp_apply S q L w).symm
      _ = 0 := by
        rw [show q.comp L = 0 from LinearMap.range_mkQ_comp L]
        simp
  have hv : v ∈ LinearMap.range L :=
    (Submodule.Quotient.mk_eq_zero (LinearMap.range L)).mp hq
  obtain ⟨e, he⟩ := hv
  rw [hL_apply] at he
  refine ⟨k, fun i j => e (i, j), n, ?_, ?_⟩
  · intro i
    exact (congrArg (fun x : T => x.1 i) he).symm
  · intro j
    exact congrArg (fun x : T => x.2 j) he

/-- Flatness reflects from scalar extension when the canonical tensor units are
injective on all modules in the test universe containing the finite-system
cokernel. The proof uses Mathlib's equational criterion for flatness. -/
theorem of_flat_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [CommRing S] [Algebra R S]
    [Module.Flat S (S ⊗[R] M)]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.Flat R M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  apply of_forall_isTrivialRelation
  intro l a m hm
  have hsR := congrArg (TensorProduct.mk R S M 1) hm
  rw [map_sum, map_zero] at hsR
  simp only [map_smul] at hsR
  have hs : ∑ i, algebraMap R S (a i) • ((1 : S) ⊗ₜ[R] m i) = 0 := by
    simpa only [TensorProduct.mk_apply, IsScalarTower.algebraMap_smul] using hsR
  obtain ⟨k, b, n, hb, hc⟩ := exists_sum_tmul_coefficients a m
    (isTrivialRelation_of_sum_smul_eq_zero hs)
  exact isTrivialRelation_of_tensor_coefficients hunit a m b n hb hc

/-- The flatness equivalence for a pure scalar extension, with injective canonical
tensor units on the test universe containing the finite-system cokernel. -/
theorem iff_flat_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [CommRing S] [Algebra R S]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M :=
  ⟨fun _ => of_flat_tensorProduct_of_injective R M S hunit, fun _ => inferInstance⟩

end Module.Flat
