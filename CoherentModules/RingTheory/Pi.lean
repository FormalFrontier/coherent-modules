/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Basic
public import CoherentModules.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.NatInt
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Coherence and finite presentation over dependent products of rings

A finite dependent product of modules is coherent over the product of its coefficient
rings exactly when every coordinate module is coherent. The scalar action is the
coordinatewise action of the given modules, not an action through a common base ring.
Specializing to the regular modules gives the corresponding criterion for coherent rings.

The proof uses the finite-generation comparison `Module.Finite.piRing_iff` and the
finite-free kernel criterion for coherence. A product-linear map from a finite free module
has coordinate maps over the individual rings; their kernels form a product linearly
equivalent to the original kernel. Conversely, a map supported at one coordinate realizes
every local kernel as a semilinear image of a product-linear kernel.

Finite presentation reflects to each coordinate for arbitrary index types. With finite
indices it is equivalent to coordinatewise finite presentation, over the original actions.
Both directions use surjective finite-free covers and finite generation of their kernels;
no coherence hypothesis on the rings or modules is needed. Additive group structures are
derived from the given module structures inside the proofs.

## References

The finite-free comparison reuses this library's `Finsupp.piLinearEquiv` formalization,
composed with Mathlib's finite-function equivalences. The proof also uses Mathlib's
finite-free basis expansion, finite-module transport, and semilinear submodule images.
-/

@[expose] public section

universe uι uR uM

namespace Module.IsCoherent

section Free

variable {ι : Type uι} (R : ι → Type uR) [_root_.Finite ι] [∀ i, Ring (R i)]

-- Compose the finite-function equivalences with the finitely supported comparison.
private noncomputable def piRingFreeEquiv (n : ℕ) :
    (Fin n → ∀ i, R i) ≃ₗ[∀ i, R i] (∀ i, Fin n → R i) := by
  let e : (∀ i, Fin n →₀ R i) ≃ₗ[∀ i, R i] (∀ i, Fin n → R i) :=
    { Equiv.piCongrRight (fun i =>
        (Finsupp.linearEquivFunOnFinite (R i) (R i) (Fin n)).toEquiv) with
      map_add' := by intro x y; ext i k; rfl
      map_smul' := by intro r x; ext i k; rfl }
  exact (Finsupp.linearEquivFunOnFinite (∀ i, R i) (∀ i, R i) (Fin n)).symm.trans
    ((Finsupp.piLinearEquiv R R).trans e)

private theorem piRingFreeEquiv_apply (n : ℕ) (x : Fin n → ∀ i, R i) (i : ι)
    (k : Fin n) : piRingFreeEquiv R n x i k = x k i := by
  change (Finsupp.piLinearEquiv R R
    ((Finsupp.linearEquivFunOnFinite (∀ i, R i) (∀ i, R i) (Fin n)).symm x) i) k = _
  simp only [Finsupp.piLinearEquiv_apply, Finsupp.linearEquivFunOnFinite_symm_apply]

private theorem piRingFreeEquiv_symm_apply (n : ℕ) (v : ∀ i, Fin n → R i)
    (k : Fin n) (i : ι) : (piRingFreeEquiv R n).symm v k i = v i k := by
  simpa only [piRingFreeEquiv_apply] using
    congrArg (fun z : ∀ i, Fin n → R i => z i k)
      ((piRingFreeEquiv R n).apply_symm_apply v)

private def piRingFreeProj (n : ℕ) (i : ι) :
    (Fin n → ∀ j, R j) →ₛₗ[Pi.evalRingHom R i] (Fin n → R i) where
  toFun x k := x k i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [_root_.Finite ι] in
private theorem piRingFreeProj_apply (n : ℕ) (i : ι) (x : Fin n → ∀ j, R j)
    (k : Fin n) : piRingFreeProj R n i x k = x k i := rfl

end Free

section Modules

variable {ι : Type uι} {R : ι → Type uR} {M : ι → Type uM}
variable [_root_.Finite ι] [∀ i, Ring (R i)]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)]

private def piRingCoordinate {n : ℕ}
    (g : (Fin n → ∀ i, R i) →ₗ[∀ i, R i] (∀ i, M i)) (i : ι) :
    (Fin n → R i) →ₗ[R i] M i :=
  Fintype.linearCombination (R i) (fun k => g (Pi.single k 1) i)

-- Basis expansion uses direct coordinate projection and does not need a finite index type.
omit [_root_.Finite ι] in
private theorem piRingCoordinate_eval {n : ℕ}
    (g : (Fin n → ∀ i, R i) →ₗ[∀ i, R i] (∀ i, M i))
    (x : Fin n → ∀ i, R i) (i : ι) :
    g x i = piRingCoordinate g i (piRingFreeProj R n i x) := by
  calc
    g x i = g (∑ k, x k • Pi.single k 1) i :=
      congrArg (fun z => g z i) (pi_eq_sum_univ' x)
    _ = ∑ k, x k i • g (Pi.single k 1) i := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply']
    _ = piRingCoordinate g i (piRingFreeProj R n i x) := by
      simp only [piRingCoordinate, Fintype.linearCombination_apply, piRingFreeProj_apply]

omit [_root_.Finite ι] in
private theorem piRingCoordinate_ker_map {n : ℕ}
    (g : (Fin n → ∀ j, R j) →ₗ[∀ j, R j] (∀ j, M j)) (i : ι) :
    (LinearMap.ker g).map (piRingFreeProj R n i) =
      LinearMap.ker (piRingCoordinate g i) := by
  classical
  -- S is a supported vector, not a unital insertion R i →+* (∀ j, R j).
  let S : (Fin n → R i) → (Fin n → ∀ j, R j) :=
    fun v k => Pi.single i (v k)
  have hs (v : Fin n → R i) :
      g (S v) = Pi.single i (piRingCoordinate g i v) := by
    funext j
    by_cases h : j = i
    · subst j
      have hp : piRingFreeProj R n i (S v) = v := by
        ext k
        simp only [piRingFreeProj_apply, S, Pi.single_eq_same]
      rw [piRingCoordinate_eval g (S v) i, hp, Pi.single_eq_same]
    · have hp : piRingFreeProj R n j (S v) = 0 := by
        ext k
        simp only [piRingFreeProj_apply, S, Pi.single_eq_of_ne h, Pi.zero_apply]
      rw [piRingCoordinate_eval g (S v) j, hp, map_zero, Pi.single_eq_of_ne h]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact (piRingCoordinate_eval g x i).symm.trans
      (congrFun (LinearMap.mem_ker.mp hx) i)
  · intro hv
    have hp : piRingFreeProj R n i (S v) = v := by
      ext k
      simp only [piRingFreeProj_apply, S, Pi.single_eq_same]
    refine Submodule.mem_map.mpr ⟨S v, ?_, hp⟩
    apply LinearMap.mem_ker.mpr
    rw [hs v, LinearMap.mem_ker.mp hv]
    funext j
    by_cases h : j = i
    · subst j
      exact Pi.single_eq_same i 0
    · exact Pi.single_eq_of_ne h 0

omit [_root_.Finite ι] in
private theorem piRingCoordinate_surjective {n : ℕ}
    (g : (Fin n → ∀ j, R j) →ₗ[∀ j, R j] (∀ j, M j))
    (hg : Function.Surjective g) (i : ι) :
    Function.Surjective (piRingCoordinate g i) := by
  classical
  intro m
  obtain ⟨x, hx⟩ := hg (Pi.single i m)
  refine ⟨piRingFreeProj R n i x, ?_⟩
  rw [← piRingCoordinate_eval g x i, hx, Pi.single_eq_same]

private theorem mem_piRingKer_iff {n : ℕ}
    (g : (Fin n → ∀ i, R i) →ₗ[∀ i, R i] (∀ i, M i))
    (x : Fin n → ∀ i, R i) :
    x ∈ LinearMap.ker g ↔
      ∀ i, piRingFreeEquiv R n x i ∈ LinearMap.ker (piRingCoordinate g i) := by
  have hproj (i : ι) : piRingFreeProj R n i x = piRingFreeEquiv R n x i := by
    ext k
    simp only [piRingFreeProj_apply, piRingFreeEquiv_apply]
  constructor
  · intro hx i
    apply LinearMap.mem_ker.mpr
    rw [← hproj i]
    exact (piRingCoordinate_eval g x i).symm.trans
      (congrFun (LinearMap.mem_ker.mp hx) i)
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext i
    rw [piRingCoordinate_eval g x i, hproj i]
    exact LinearMap.mem_ker.mp (hx i)

private noncomputable def piRingKerEquiv {n : ℕ}
    (g : (Fin n → ∀ i, R i) →ₗ[∀ i, R i] (∀ i, M i)) :
    LinearMap.ker g ≃ₗ[∀ i, R i] (∀ i, LinearMap.ker (piRingCoordinate g i)) where
  toFun x i := ⟨piRingFreeEquiv R n x.1 i, (mem_piRingKer_iff g x.1).mp x.2 i⟩
  invFun v := ⟨(piRingFreeEquiv R n).symm (fun i => (v i).1), by
    apply (mem_piRingKer_iff g _).mpr
    intro i
    have hi := congrFun ((piRingFreeEquiv R n).apply_symm_apply (fun i => (v i).1)) i
    rw [hi]
    exact (v i).2⟩
  left_inv x := by
    apply Subtype.ext
    exact (piRingFreeEquiv R n).symm_apply_apply x.1
  right_inv v := by
    funext i
    apply Subtype.ext
    funext k
    simp only [piRingFreeEquiv_apply, piRingFreeEquiv_symm_apply]
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact congrFun ((piRingFreeEquiv R n).map_add x.1 y.1) i
  map_smul' r x := by
    funext i
    apply Subtype.ext
    exact congrFun ((piRingFreeEquiv R n).map_smul r x.1) i

private noncomputable def piRingSupportedMap {n : ℕ} (i : ι)
    (f : (Fin n → R i) →ₗ[R i] M i) :
    (Fin n → ∀ j, R j) →ₗ[∀ j, R j] (∀ j, M j) := by
  classical
  refine
    { toFun := fun x => Pi.single i (f (piRingFreeProj R n i x))
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    change (AddMonoidHom.single M i) (f (piRingFreeProj R n i (x + y))) =
      (AddMonoidHom.single M i) (f (piRingFreeProj R n i x)) +
        (AddMonoidHom.single M i) (f (piRingFreeProj R n i y))
    simp only [map_add]
  · intro r x
    rw [(piRingFreeProj R n i).map_smulₛₗ, f.map_smul]
    ext j
    by_cases h : j = i
    · subst j
      simp only [Pi.smul_apply', Pi.single_eq_same]; rfl
    · simp only [Pi.smul_apply', Pi.single_eq_of_ne h, smul_zero]

omit [_root_.Finite ι] in
private theorem piRingSupportedMap_apply_same {n : ℕ} (i : ι)
    (f : (Fin n → R i) →ₗ[R i] M i) (x : Fin n → ∀ j, R j) :
    piRingSupportedMap i f x i = f (piRingFreeProj R n i x) := by
  classical
  change (Pi.single i (f (piRingFreeProj R n i x))) i = _
  exact Pi.single_eq_same i _

omit [_root_.Finite ι] in
private theorem piRingSupportedMap_apply_ne {n : ℕ} (i : ι)
    (f : (Fin n → R i) →ₗ[R i] M i) (x : Fin n → ∀ j, R j) {j : ι}
    (h : j ≠ i) : piRingSupportedMap i f x j = 0 := by
  classical
  change (Pi.single i (f (piRingFreeProj R n i x))) j = _
  exact Pi.single_eq_of_ne h _

omit [_root_.Finite ι] in
private theorem piRingSupportedMap_ker_map {n : ℕ} (i : ι)
    (f : (Fin n → R i) →ₗ[R i] M i) :
    (LinearMap.ker (piRingSupportedMap i f)).map (piRingFreeProj R n i) =
      LinearMap.ker f := by
  classical
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    simpa only [piRingSupportedMap_apply_same, Pi.zero_apply] using
      congrFun (LinearMap.mem_ker.mp hx) i
  · intro hv
    let x : Fin n → ∀ j, R j := fun k => Pi.single i (v k)
    have hpx : piRingFreeProj R n i x = v := by
      ext k
      simp only [piRingFreeProj_apply, x, Pi.single_eq_same]
    refine Submodule.mem_map.mpr ⟨x, ?_, hpx⟩
    apply LinearMap.mem_ker.mpr
    funext j
    by_cases h : j = i
    · subst j
      rw [piRingSupportedMap_apply_same, hpx, LinearMap.mem_ker.mp hv]
      rfl
    · exact piRingSupportedMap_apply_ne i f x h

end Modules

section OriginalMonoids

variable {ι : Type uι} {R : ι → Type uR} {M : ι → Type uM}
variable [_root_.Finite ι] [∀ i, Ring (R i)]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)]

/-- A finite dependent product is coherent over its product coefficient ring exactly when
all coordinate modules are coherent over their given coefficient rings. The module carriers
need only their given additive commutative monoid structures. The action on the product is
`(r • m) i = r i • m i`; no commutativity or nontriviality is required. -/
theorem piRing_iff :
    Module.IsCoherent (∀ i, R i) (∀ i, M i) ↔ ∀ i, Module.IsCoherent (R i) (M i) := by
  let : ∀ i, AddCommGroup (M i) := fun i =>
    Module.addCommMonoidToAddCommGroup (R i) (M := M i)
  constructor
  · intro h i
    obtain ⟨hfinite, hker⟩ := iff_finite_and_fg_ker.mp h
    refine iff_finite_and_fg_ker.mpr
      ⟨(Module.Finite.piRing_iff (R := R) (M := M)).mp hfinite i, ?_⟩
    intro n f
    have hfg := (hker n (piRingSupportedMap i f)).map (piRingFreeProj R n i)
    rwa [piRingSupportedMap_ker_map] at hfg
  · intro h
    apply iff_finite_and_fg_ker.mpr
    refine ⟨(Module.Finite.piRing_iff (R := R) (M := M)).mpr
      (fun i => (iff_finite_and_fg_ker.mp (h i)).1), ?_⟩
    intro n g
    have hfinite : ∀ i, Module.Finite (R i) (LinearMap.ker (piRingCoordinate g i)) := by
      intro i
      exact Module.Finite.of_fg
        ((iff_finite_and_fg_ker.mp (h i)).2 n (piRingCoordinate g i))
    let _ : Module.Finite (∀ i, R i) (∀ i, LinearMap.ker (piRingCoordinate g i)) :=
      (Module.Finite.piRing_iff (R := R)
        (M := fun i => LinearMap.ker (piRingCoordinate g i))).mpr hfinite
    exact Module.Finite.iff_fg.mp (Module.Finite.equiv (piRingKerEquiv g).symm)

end OriginalMonoids

end Module.IsCoherent

/-- A finite dependent product of possibly noncommutative rings is coherent exactly when
every factor is coherent. This is the regular-module specialization of
`Module.IsCoherent.piRing_iff`, and includes empty products and zero rings. -/
theorem isCoherentRing_pi_iff {ι : Type uι} {R : ι → Type uR}
    [Finite ι] [∀ i, Ring (R i)] :
    IsCoherentRing (∀ i, R i) ↔ ∀ i, IsCoherentRing (R i) := by
  constructor
  · intro h
    let _ := h
    have hm := (Module.IsCoherent.piRing_iff (R := R) (M := R)).mp inferInstance
    exact fun i => ⟨hm i⟩
  · intro h
    let _ : ∀ i, IsCoherentRing (R i) := h
    exact ⟨(Module.IsCoherent.piRing_iff (R := R) (M := R)).mpr fun _ => inferInstance⟩

namespace Module.FinitePresentation

section OriginalMonoids

variable {ι : Type uι} (R : ι → Type uR) (M : ι → Type uM)
variable [∀ i, Ring (R i)]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)]

/-- Finite presentation over a dependent product of rings implies finite presentation at
each coordinate, for an arbitrary index type and the given coordinate actions. -/
theorem of_piRing [Module.FinitePresentation (∀ i, R i) (∀ i, M i)] (i : ι) :
    Module.FinitePresentation (R i) (M i) := by
  classical
  -- Over a ring, the given additive monoid has a canonical compatible group structure.
  let : ∀ j, AddCommGroup (M j) := fun j =>
    Module.addCommMonoidToAddCommGroup (R j) (M := M j)
  -- Choose a finite-free presentation of the product module.
  have cover : ∃ (n m : ℕ)
      (g : (Fin n → ∀ j, R j) →ₗ[∀ j, R j] (∀ j, M j))
      (f : (Fin m → ∀ j, R j) →ₗ[∀ j, R j] (Fin n → ∀ j, R j)),
      Function.Surjective g ∧ Function.Exact f g :=
    Module.FinitePresentation.exists_fin' (∀ j, R j) (∀ j, M j)
  obtain ⟨n, _m, g, _f, hg, _hfg⟩ := cover
  let P : (Fin n → ∀ j, R j) →ₛₗ[Pi.evalRingHom R i] (Fin n → R i) :=
    Module.IsCoherent.piRingFreeProj R n i
  let gi : (Fin n → R i) →ₗ[R i] M i :=
    Module.IsCoherent.piRingCoordinate g i
  let K : Submodule (∀ j, R j) (Fin n → ∀ j, R j) := LinearMap.ker g
  let Ki : Submodule (R i) (Fin n → R i) := LinearMap.ker gi
  have hK : K.FG := Module.FinitePresentation.fg_ker g hg
  have hgi : Function.Surjective gi :=
    Module.IsCoherent.piRingCoordinate_surjective g hg i
  have hcomparison : K.map P = Ki :=
    Module.IsCoherent.piRingCoordinate_ker_map g i
  have hKi : Ki.FG := by
    rw [← hcomparison]
    exact hK.map P
  exact Module.finitePresentation_of_free_of_surjective gi hgi hKi

/-- A finite dependent product is finitely presented over its product coefficient ring
exactly when each coordinate module is finitely presented over its given ring. The module
carriers need only their given additive commutative monoid structures. -/
theorem piRing_iff [_root_.Finite ι] :
    Module.FinitePresentation (∀ i, R i) (∀ i, M i) ↔
      ∀ i, Module.FinitePresentation (R i) (M i) := by
  constructor
  · intro h
    let : Module.FinitePresentation (∀ i, R i) (∀ i, M i) := h
    exact fun i => of_piRing R M i
  · intro h
    classical
    let : ∀ i, AddCommGroup (M i) := fun i =>
      Module.addCommMonoidToAddCommGroup (R i) (M := M i)
    -- Local finite-free presentations first give finite generation of the product.
    have hfinite (i : ι) : Module.Finite (R i) (M i) := by
      let : Module.FinitePresentation (R i) (M i) := h i
      have localCover : ∃ (n m : ℕ) (gi : (Fin n → R i) →ₗ[R i] M i)
          (fi : (Fin m → R i) →ₗ[R i] (Fin n → R i)),
          Function.Surjective gi ∧ Function.Exact fi gi :=
        Module.FinitePresentation.exists_fin' (R i) (M i)
      obtain ⟨_n, _m, gi, _fi, hgi, _hfigi⟩ := localCover
      exact Module.Finite.of_surjective gi hgi
    let : Module.Finite (∀ i, R i) (∀ i, M i) :=
      (Module.Finite.piRing_iff (R := R) (M := M)).mpr hfinite
    -- Compare the kernel of a global finite-free cover with its coordinate kernels.
    have cover : ∃ (n : ℕ)
        (g : (Fin n → ∀ i, R i) →ₗ[∀ i, R i] (∀ i, M i)), Function.Surjective g :=
      Module.Finite.exists_fin' (∀ i, R i) (∀ i, M i)
    obtain ⟨n, g, hg⟩ := cover
    let gi (i : ι) : (Fin n → R i) →ₗ[R i] M i :=
      Module.IsCoherent.piRingCoordinate g i
    let Ki (i : ι) : Submodule (R i) (Fin n → R i) := LinearMap.ker (gi i)
    let K : Submodule (∀ i, R i) (Fin n → ∀ i, R i) := LinearMap.ker g
    let E : K ≃ₗ[∀ i, R i] (∀ i, Ki i) := Module.IsCoherent.piRingKerEquiv g
    have hgi (i : ι) : Function.Surjective (gi i) :=
      Module.IsCoherent.piRingCoordinate_surjective g hg i
    have hKi (i : ι) : (Ki i).FG := by
      let : Module.FinitePresentation (R i) (M i) := h i
      exact Module.FinitePresentation.fg_ker (gi i) (hgi i)
    have hfiniteKi (i : ι) : Module.Finite (R i) (Ki i) :=
      Module.Finite.of_fg (hKi i)
    let : Module.Finite (∀ i, R i) (∀ i, Ki i) :=
      (Module.Finite.piRing_iff (R := R) (M := fun i => Ki i)).mpr hfiniteKi
    have hK : K.FG := Module.Finite.iff_fg.mp (Module.Finite.equiv E.symm)
    exact Module.finitePresentation_of_free_of_surjective g hg hK

end OriginalMonoids

end Module.FinitePresentation
