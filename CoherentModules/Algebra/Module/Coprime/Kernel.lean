/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.DirectSum.Idempotents
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coprime kernels of a semiring representation

Let `τ : A →+* Module.End R M`, where `A` is a commutative semiring. A finite
pairwise Bézout-coprime family `a` whose product acts as zero gives an `R`-linear
equivalence of `M` with the product of the kernels of `τ (a i)`. Its inverse is
the sum of the kernel inclusions. The scalar semiring `R` need not be commutative,
and `M` needs neither subtraction nor cancellation.

The coordinate projectors are `τ (μ i * ∏ j ∈ {i}ᶜ, a j)` for **any** coefficients
with `∑ i, μ i * ∏ j ∈ {i}ᶜ, a j = 1`. Thus their values do not depend on the
Bézout witnesses. The coefficient image is commutative, but the projectors need not
be central in the full endomorphism semiring.

Empty indices are allowed: the annihilation premise then says that the identity
endomorphism is zero. A partition of unity in `A` is not required in this case.
Unit factors give zero kernels; zero factors are allowed under coprimality.

The Bézout witnesses are encapsulated: use the coordinate and reconstruction
formulas rather than unfolding the constructions.

An additive map intertwining just the labelled annihilating operators also
intertwines the canonical kernel projectors and preserves the underlying values of
the kernel-equivalence coordinates. The coefficient and scalar semirings on the
two sides may differ; no scalar-linearity or compatibility with other represented
elements is assumed.

More generally, labels may be regrouped by an arbitrary map between finite index
sets: intertwining each fibre-product with its target annihilating operator
intertwines the sum of the fine kernel projectors over that fibre with the target
projector. The target coordinate is the corresponding sum of mapped fine
coordinates. Empty fibres are allowed, and the label map need not be injective or
surjective.

For example, multiplication on `ℕ × ℕ` with factors `(1, 0)` and `(0, 1)` has
labelled kernel projectors `(x, y) ↦ (0, y)` and `(x, y) ↦ (x, 0)`, respectively.
No additive inverses are present in this example.

Polynomial specialization uses `Polynomial.eval₂RingHom'`: coefficients need only
commute with the selected endomorphism. Scalar specialization uses
`Module.toModuleEnd` and identifies the kernels with `Submodule.torsionBy`.

## References

The construction uses Mathlib's complete complementary-product Bézout identity
`exists_sum_eq_one_iff_pairwise_coprime'`, its `CompleteOrthogonalIdempotents`,
linear-map kernels and product equivalences. The scalar comparison follows
Mathlib's `Submodule.torsionBy_isInternal`; the semiring kernel result generalizes
that theorem beyond its commutative-ring and additive-group hypotheses. Additive
intertwining uses `OrthogonalIdempotents.semiconj_iff_mapsTo_range` and the canonical
`Module.toAddMonoidEnd` action on the kernel projectors.
-/

public section

universe uR uT uM uN uA uB uI uJ

namespace RingHom

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {A : Type uA} [CommSemiring A]
variable {ι : Type uI} [Fintype ι]

-- For a nonempty index type, the coefficients form a complementary-product Bézout
-- partition of unity; for an empty index type, the coefficient function is zero.
private noncomputable def coprimeCoefficients [DecidableEq ι] (a : ι → A)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j)) : ι → A :=
  letI : Decidable (Nonempty ι) := Classical.propDecidable _
  if h : Nonempty ι then
    letI : Nonempty ι := h
    Classical.choose ((exists_sum_eq_one_iff_pairwise_coprime' (s := a)).2 hcop)
  else fun _ ↦ 0

-- The annihilation premise is deliberately absent from these endomorphism data.
private def partitionEnd [DecidableEq ι] (τ : A →+* Module.End R M)
    (a μ : ι → A) (i : ι) :
    Module.End R M :=
  τ (μ i * ∏ j ∈ {i}ᶜ, a j)

private noncomputable def coprimeEnd (τ : A →+* Module.End R M) (a : ι → A)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j)) (i : ι) : Module.End R M := by
  classical
  exact partitionEnd τ a (coprimeCoefficients a hcop) i

private theorem sum_partitionEnd [DecidableEq ι]
    (τ : A →+* Module.End R M) (a μ : ι → A)
    (hμ : (∑ i, μ i * ∏ j ∈ {i}ᶜ, a j) = 1) :
    (∑ i, partitionEnd τ a μ i) = 1 := by
  simp only [partitionEnd, ← map_sum, hμ, map_one]

private theorem coprimeCoefficients_partition [DecidableEq ι] [Nonempty ι]
    (a : ι → A) (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j)) :
    (∑ i, coprimeCoefficients a hcop i * ∏ j ∈ {i}ᶜ, a j) = 1 := by
  simpa only [coprimeCoefficients, dite_eq_left (show Nonempty ι from inferInstance)] using
    Classical.choose_spec ((exists_sum_eq_one_iff_pairwise_coprime' (s := a)).2 hcop)

-- Complementary products land in their labelled kernel and separate the other kernels.
private theorem partitionEnd_mem_ker [DecidableEq ι]
    (τ : A →+* Module.End R M) (a μ : ι → A)
    (hAnn : τ (∏ i, a i) = 0) (i : ι) (x : M) :
    partitionEnd τ a μ i x ∈ LinearMap.ker (τ (a i)) := by
  have hmul : a i * (μ i * ∏ j ∈ {i}ᶜ, a j) = μ i * ∏ j, a j := by
    rw [mul_left_comm, ← Fintype.prod_eq_mul_prod_compl i a]
  rw [LinearMap.mem_ker]
  change (τ (a i) * τ (μ i * ∏ j ∈ {i}ᶜ, a j)) x = 0
  rw [← map_mul, hmul, map_mul, hAnn, mul_zero]
  rfl

private theorem partitionEnd_apply_eq_zero_of_mem_ker [DecidableEq ι]
    (τ : A →+* Module.End R M) (a μ : ι → A) {i j : ι}
    (hij : i ≠ j) (x : M) (hx : x ∈ LinearMap.ker (τ (a j))) :
    partitionEnd τ a μ i x = 0 := by
  have hj : j ∈ ({i}ᶜ : Finset ι) := by simpa using hij.symm
  unfold partitionEnd
  rw [Finset.prod_eq_prod_sdiff_singleton_mul hj a, ← mul_assoc, map_mul,
    Module.End.mul_apply, LinearMap.mem_ker.mp hx, map_zero]

private theorem partitionEnd_apply_eq_self_of_mem_ker [DecidableEq ι]
    (τ : A →+* Module.End R M) (a μ : ι → A)
    (hμ : (∑ i, μ i * ∏ j ∈ {i}ᶜ, a j) = 1) (i : ι) (x : M)
    (hx : x ∈ LinearMap.ker (τ (a i))) :
    partitionEnd τ a μ i x = x := by
  have hsingle : (∑ j, partitionEnd τ a μ j x) = partitionEnd τ a μ i x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact partitionEnd_apply_eq_zero_of_mem_ker τ a μ hji x hx
    · simp
  simpa only [LinearMap.sum_apply, Module.End.one_apply, hsingle] using
    LinearMap.congr_fun (sum_partitionEnd τ a μ hμ) x

-- Completeness and identification of the ranges with the kernels.
private theorem coprimeEnd_complete (τ : A →+* Module.End R M) (a : ι → A)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hAnn : τ (∏ i, a i) = 0) :
    CompleteOrthogonalIdempotents (coprimeEnd τ a hcop) := by
  classical
  apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply LinearMap.ext
    intro x
    change partitionEnd τ a (coprimeCoefficients a hcop) i
      (partitionEnd τ a (coprimeCoefficients a hcop) j x) = 0
    exact partitionEnd_apply_eq_zero_of_mem_ker τ a _ hij _
      (partitionEnd_mem_ker τ a _ hAnn j x)
  · by_cases hι : Nonempty ι
    · let : Nonempty ι := hι
      exact sum_partitionEnd τ a _ (coprimeCoefficients_partition a hcop)
    · let : IsEmpty ι := ⟨fun i ↦ hι ⟨i⟩⟩
      simpa using hAnn.symm

private theorem coprimeEnd_range (τ : A →+* Module.End R M) (a : ι → A)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hAnn : τ (∏ i, a i) = 0) (i : ι) :
    LinearMap.range (coprimeEnd τ a hcop i) = LinearMap.ker (τ (a i)) := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact partitionEnd_mem_ker τ a _ hAnn i y
  · intro x hx
    let : Nonempty ι := ⟨i⟩
    exact LinearMap.mem_range.mpr ⟨x,
      partitionEnd_apply_eq_self_of_mem_ker τ a _
        (coprimeCoefficients_partition a hcop) i x hx⟩

/-- The kernel decomposition for pairwise Bézout-coprime elements of a represented
commutative semiring, assuming only annihilation by their product. The forward map
has coordinates `τ (μ i * ∏ j ∈ {i}ᶜ, a j)` for a whole Bézout partition when the
index is nonempty. The inverse sums the kernel inclusions, including for empty indices.

The range equivalence supplies the inverse laws; the subsequent equivalences of equal
submodules act identically on underlying elements. -/
noncomputable def linearEquivPiKer (τ : A →+* Module.End R M) (a : ι → A)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hAnn : τ (∏ i, a i) = 0) : M ≃ₗ[R] (∀ i, LinearMap.ker (τ (a i))) :=
  (CompleteOrthogonalIdempotents.linearEquivPiRange
    (P := coprimeEnd τ a hcop) (by exact coprimeEnd_complete τ a hcop hAnn)).trans
    (LinearEquiv.piCongrRight fun i ↦
      LinearEquiv.ofEq _ _ (by exact coprimeEnd_range τ a hcop hAnn i))

/-- The canonical projector onto one of the coprime kernels, obtained by applying a
coordinate of the kernel equivalence and then including that kernel in `M`. -/
noncomputable def kerProjector (τ : A →+* Module.End R M) (a : ι → A)
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hAnn : τ (∏ i, a i) = 0) (i : ι) : Module.End R M :=
  (LinearMap.ker (τ (a i))).subtype.comp
    ((LinearMap.proj i).comp (τ.linearEquivPiKer a hcop hAnn).toLinearMap)

variable (τ : A →+* Module.End R M) (a : ι → A)
variable (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
variable (hAnn : τ (∏ i, a i) = 0)

/-- A coordinate of the kernel equivalence is the corresponding kernel projector. -/
@[simp]
theorem linearEquivPiKer_apply (x : M) (i : ι) :
    (τ.linearEquivPiKer a hcop hAnn x i : M) = τ.kerProjector a hcop hAnn i x := by
  rfl

-- Equality transports between the ranges and kernels preserve underlying elements.
private theorem kerProjector_eq_coprimeEnd (i : ι) :
    τ.kerProjector a hcop hAnn i = coprimeEnd τ a hcop i := by
  apply LinearMap.ext
  intro x
  rfl

/-- The inverse kernel equivalence is the finite sum of the subtype inclusions. -/
@[simp]
theorem linearEquivPiKer_symm_apply (x : ∀ i, LinearMap.ker (τ (a i))) :
    (τ.linearEquivPiKer a hcop hAnn).symm x = ∑ i, (x i : M) := by
  change
    (CompleteOrthogonalIdempotents.linearEquivPiRange
      (coprimeEnd_complete τ a hcop hAnn)).symm
      (fun i ↦ (LinearEquiv.ofEq _ _ (coprimeEnd_range τ a hcop hAnn i)).symm (x i)) = _
  rw [CompleteOrthogonalIdempotents.linearEquivPiRange_symm_apply]
  rfl

/-- A kernel element has itself as its own coordinate. -/
@[simp]
theorem linearEquivPiKer_apply_coe_same (i : ι) (x : LinearMap.ker (τ (a i))) :
    τ.linearEquivPiKer a hcop hAnn (x : M) i = x := by
  apply Subtype.ext
  rw [linearEquivPiKer_apply, kerProjector_eq_coprimeEnd]
  have hx : (x : M) ∈ LinearMap.range (coprimeEnd τ a hcop i) := by
    rw [coprimeEnd_range τ a hcop hAnn i]
    exact x.property
  exact congrArg Subtype.val
    ((coprimeEnd_complete τ a hcop hAnn).linearEquivPiRange_apply_coe_same i ⟨x, hx⟩)

/-- An element of one kernel has zero coordinate in every other kernel. -/
@[simp]
theorem linearEquivPiKer_apply_coe_ne {i j : ι} (hij : i ≠ j)
    (x : LinearMap.ker (τ (a i))) :
    τ.linearEquivPiKer a hcop hAnn (x : M) j = 0 := by
  apply Subtype.ext
  rw [linearEquivPiKer_apply, kerProjector_eq_coprimeEnd]
  have hx : (x : M) ∈ LinearMap.range (coprimeEnd τ a hcop i) := by
    rw [coprimeEnd_range τ a hcop hAnn i]
    exact x.property
  exact congrArg Subtype.val
    ((coprimeEnd_complete τ a hcop hAnn).linearEquivPiRange_apply_coe_ne hij ⟨x, hx⟩)

/-- Each kernel projector takes values in its labelled kernel. -/
theorem kerProjector_mem (i : ι) (x : M) :
    τ.kerProjector a hcop hAnn i x ∈ LinearMap.ker (τ (a i)) := by
  rw [← linearEquivPiKer_apply]
  exact (τ.linearEquivPiKer a hcop hAnn x i).property

/-- Membership in a coprime kernel is equivalent to being fixed by its projector. -/
theorem mem_ker_iff_kerProjector_eq_self (i : ι) (x : M) :
    x ∈ LinearMap.ker (τ (a i)) ↔ τ.kerProjector a hcop hAnn i x = x := by
  constructor
  · intro hx
    simpa only [linearEquivPiKer_apply] using congrArg Subtype.val
      (τ.linearEquivPiKer_apply_coe_same a hcop hAnn i ⟨x, hx⟩)
  · intro hx
    rw [← hx]
    exact τ.kerProjector_mem a hcop hAnn i x

/-- The image of a kernel projector is exactly the corresponding kernel. -/
@[simp]
theorem range_kerProjector (i : ι) :
    LinearMap.range (τ.kerProjector a hcop hAnn i) = LinearMap.ker (τ (a i)) := by
  rw [kerProjector_eq_coprimeEnd]
  exact coprimeEnd_range τ a hcop hAnn i

/-- Each kernel projector is a projection onto its labelled kernel. -/
theorem isProj_kerProjector (i : ι) :
    LinearMap.IsProj (LinearMap.ker (τ (a i))) (τ.kerProjector a hcop hAnn i) := by
  exact ⟨τ.kerProjector_mem a hcop hAnn i,
    fun x hx ↦ (τ.mem_ker_iff_kerProjector_eq_self a hcop hAnn i x).mp hx⟩

/-- The canonical kernel projectors are complete orthogonal idempotents. -/
theorem kerProjector_completeOrthogonalIdempotents :
    CompleteOrthogonalIdempotents (τ.kerProjector a hcop hAnn) := by
  have hP : τ.kerProjector a hcop hAnn = coprimeEnd τ a hcop := by
    funext i
    exact kerProjector_eq_coprimeEnd τ a hcop hAnn i
  rw [hP]
  exact coprimeEnd_complete τ a hcop hAnn

/-- Each kernel projector is idempotent. -/
theorem kerProjector_idempotent (i : ι) :
    IsIdempotentElem (τ.kerProjector a hcop hAnn i) := by
  exact (τ.kerProjector_completeOrthogonalIdempotents a hcop hAnn).idem i

/-- Distinct labelled kernel projectors annihilate one another. -/
theorem kerProjector_mul_of_ne {i j : ι} (hij : i ≠ j) :
    τ.kerProjector a hcop hAnn i * τ.kerProjector a hcop hAnn j = 0 := by
  exact (τ.kerProjector_completeOrthogonalIdempotents a hcop hAnn).ortho hij

/-- The sum of the kernel projectors is the identity endomorphism. -/
@[simp]
theorem sum_kerProjector : ∑ i, τ.kerProjector a hcop hAnn i = 1 := by
  exact (τ.kerProjector_completeOrthogonalIdempotents a hcop hAnn).complete

/-- Every complementary-product Bézout partition gives the canonical kernel projectors.
This does not require a nonempty index hypothesis: whenever a partition exists, the
formula holds. In the empty case no partition is needed to construct the equivalence. -/
theorem kerProjector_eq_of_bezout [DecidableEq ι] (μ : ι → A)
    (hμ : (∑ i, μ i * ∏ j ∈ {i}ᶜ, a j) = 1) (i : ι) :
    τ.kerProjector a hcop hAnn i = τ (μ i * ∏ j ∈ {i}ᶜ, a j) := by
  apply LinearMap.ext
  intro x
  change τ.kerProjector a hcop hAnn i x = partitionEnd τ a μ i x
  calc
    τ.kerProjector a hcop hAnn i x = (τ.linearEquivPiKer a hcop hAnn x i : M) :=
      (τ.linearEquivPiKer_apply a hcop hAnn x i).symm
    _ = partitionEnd τ a μ i (∑ j, (τ.linearEquivPiKer a hcop hAnn x j : M)) := by
      rw [map_sum, Finset.sum_eq_single i]
      · exact (partitionEnd_apply_eq_self_of_mem_ker τ a μ hμ i _
          (τ.linearEquivPiKer a hcop hAnn x i).property).symm
      · intro j _ hji
        exact partitionEnd_apply_eq_zero_of_mem_ker τ a μ hji.symm _
          (τ.linearEquivPiKer a hcop hAnn x j).property
      · simp
    _ = partitionEnd τ a μ i x := by
      rw [← linearEquivPiKer_symm_apply τ a hcop hAnn, LinearEquiv.symm_apply_apply]

/-- Two valid whole Bézout partitions give the same labelled endomorphism, not just
the same image submodule. -/
theorem bezout_projector_eq [DecidableEq ι]
    (hAnn : τ (∏ i, a i) = 0) (μ ν : ι → A)
    (hμ : (∑ i, μ i * ∏ j ∈ {i}ᶜ, a j) = 1)
    (hν : (∑ i, ν i * ∏ j ∈ {i}ᶜ, a j) = 1) (i : ι) :
    τ (μ i * ∏ j ∈ {i}ᶜ, a j) = τ (ν i * ∏ j ∈ {i}ᶜ, a j) := by
  let : Nonempty ι := ⟨i⟩
  have hcop : Pairwise fun j k ↦ IsCoprime (a j) (a k) :=
    (exists_sum_eq_one_iff_pairwise_coprime' (s := a)).mp ⟨μ, hμ⟩
  exact (τ.kerProjector_eq_of_bezout a hcop hAnn μ hμ i).symm.trans
    (τ.kerProjector_eq_of_bezout a hcop hAnn ν hν i)

/-- On a direct sum, the inverse kernel equivalence is the canonical inclusion-and-sum
map, with the caller's equality dictionary. -/
theorem linearEquivPiKer_symm_comp_coeFnLinearMap [DecidableEq ι] :
    (τ.linearEquivPiKer a hcop hAnn).symm.toLinearMap.comp (DirectSum.coeFnLinearMap R) =
      DirectSum.coeLinearMap (fun i ↦ LinearMap.ker (τ (a i))) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  have hcoe : DirectSum.coeFnLinearMap R
      (DirectSum.lof R ι (fun i ↦ LinearMap.ker (τ (a i))) i x) = Pi.single i x :=
    rfl
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearEquiv.coe_coe]
  rw [hcoe, linearEquivPiKer_symm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- The coprime kernels form an internal direct sum under their subtype inclusions. -/
theorem isInternal_ker [DecidableEq ι]
    (hcop : Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hAnn : τ (∏ i, a i) = 0) :
    DirectSum.IsInternal (fun i ↦ LinearMap.ker (τ (a i))) := by
  have hbij : Function.Bijective
      ((τ.linearEquivPiKer a hcop hAnn).symm.toLinearMap.comp (DirectSum.coeFnLinearMap R)) :=
    (τ.linearEquivPiKer a hcop hAnn).symm.bijective.comp
      (DirectSum.linearEquivFunOnFintype R ι (fun i ↦ LinearMap.ker (τ (a i)))).bijective
  rw [τ.linearEquivPiKer_symm_comp_coeFnLinearMap a hcop hAnn] at hbij
  exact hbij

section Naturality

variable {T : Type uT} [Semiring T]
variable {N : Type uN} [AddCommMonoid N] [Module T N]
variable {B : Type uB} [CommSemiring B]

section Fiberwise

variable {J : Type uJ} [Fintype J] [DecidableEq J]

/-- An additive map intertwines the sums of fine canonical kernel projectors over each
fibre with the corresponding target kernel projectors if and only if it sends each fine
kernel into the target kernel at its image label. The label map is arbitrary, and empty
fibres contribute zero. No scalar-linearity or intertwining of the annihilating operators
is required. -/
theorem semiconj_sum_kerProjector_iff_mapsTo_ker
    (υ : B →+* Module.End T N) (b : J → B)
    (hcop' : Pairwise fun j k ↦ IsCoprime (b j) (b k))
    (hAnn' : υ (∏ j, b j) = 0)
    (q : ι → J) (h : M →+ N) :
    (∀ j, Function.Semiconj h
      (∑ i with q i = j, τ.kerProjector a hcop hAnn i : Module.End R M)
      (υ.kerProjector b hcop' hAnn' j)) ↔
      ∀ i, Set.MapsTo h (LinearMap.ker (τ (a i)) : Set M)
        (LinearMap.ker (υ (b (q i))) : Set N) := by
  classical
  let F : Module.End R M →+* AddMonoid.End M :=
    Module.toAddMonoidEnd (Module.End R M) M
  let G : Module.End T N →+* AddMonoid.End N :=
    Module.toAddMonoidEnd (Module.End T N) N
  have hP := (τ.kerProjector_completeOrthogonalIdempotents a hcop hAnn).map F
  have hQ := (υ.kerProjector_completeOrthogonalIdempotents b hcop' hAnn').map G
  have hPrange (i : ι) : Set.range (F (τ.kerProjector a hcop hAnn i)) =
      (LinearMap.ker (τ (a i)) : Set M) :=
    congrArg (fun S : Submodule R M ↦ (S : Set M))
      (τ.range_kerProjector a hcop hAnn i)
  have hQrange (j : J) : Set.range (G (υ.kerProjector b hcop' hAnn' j)) =
      (LinearMap.ker (υ (b j)) : Set N) :=
    congrArg (fun S : Submodule T N ↦ (S : Set N))
      (υ.range_kerProjector b hcop' hAnn' j)
  have hsum_apply (j : J) (x : M) :
      ∑ i with q i = j, (F (τ.kerProjector a hcop hAnn i)) x =
        (∑ i with q i = j, τ.kerProjector a hcop hAnn i : Module.End R M) x := by
    calc
      _ = (F (∑ i with q i = j, τ.kerProjector a hcop hAnn i)) x := by
        rw [map_sum]
        exact (AddMonoidHom.finsetSum_apply (fun i ↦ F (τ.kerProjector a hcop hAnn i))
          (Finset.univ.filter fun i ↦ q i = j) x).symm
      _ = _ := rfl
  have he := hP.semiconj_sum_fiberwise_iff_mapsTo_range hQ.toOrthogonalIdempotents q h
  simp only [Function.comp_apply, Function.Semiconj, Finset.sum_apply,
    hsum_apply, hPrange, hQrange] at he
  exact he

/-- An additive map intertwining each product of fine annihilating factors over a fibre
with the corresponding target annihilating operator intertwines the sum of the fine
canonical kernel projectors over that fibre with the target kernel projector.
The label map is arbitrary, and empty fibres contribute the identity factor-product
and the zero projector sum. No scalar-linearity or compatibility with other
represented elements is required. -/
theorem semiconj_sum_kerProjector
    (υ : B →+* Module.End T N) (b : J → B)
    (hcop' : Pairwise fun j k ↦ IsCoprime (b j) (b k))
    (hAnn' : υ (∏ j, b j) = 0)
    (q : ι → J) (h : M →+ N)
    (hh : ∀ j, Function.Semiconj h (τ (∏ i with q i = j, a i)) (υ (b j))) :
    ∀ j, Function.Semiconj h
      (∑ i with q i = j, τ.kerProjector a hcop hAnn i : Module.End R M)
      (υ.kerProjector b hcop' hAnn' j) := by
  classical
  let F : Module.End R M →+* AddMonoid.End M :=
    Module.toAddMonoidEnd (Module.End R M) M
  let G : Module.End T N →+* AddMonoid.End N :=
    Module.toAddMonoidEnd (Module.End T N) N
  have hP :=
    ((τ.kerProjector_completeOrthogonalIdempotents a hcop hAnn).sum_fiberwise q).map F
  have hQ := (υ.kerProjector_completeOrthogonalIdempotents b hcop' hAnn').map G
  apply (hQ.toOrthogonalIdempotents.semiconj_iff_mapsTo_range hP.complete h).mpr
  intro j x hx
  obtain ⟨y, rfl⟩ := hx
  -- Every factor in the fibre kills its own fine-projector value, so the product
  -- kills the sum of those values.
  have hzero : τ (∏ i with q i = j, a i)
      ((∑ i with q i = j, τ.kerProjector a hcop hAnn i : Module.End R M) y) = 0 := by
    rw [LinearMap.sum_apply, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.prod_erase_mul _ a hi, map_mul, Module.End.mul_apply,
      LinearMap.mem_ker.mp (τ.kerProjector_mem a hcop hAnn i y), map_zero]
  have hker : h ((∑ i with q i = j, τ.kerProjector a hcop hAnn i : Module.End R M) y) ∈
      LinearMap.ker (υ (b j)) := by
    rw [LinearMap.mem_ker, ← hh j _, hzero, map_zero]
  rw [← υ.range_kerProjector b hcop' hAnn' j] at hker
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hker
  exact ⟨z, hz⟩

/-- After an additive map intertwines each fibre-product of fine annihilating factors
with its target annihilating operator, the underlying target kernel coordinate is
the sum over that fibre of the mapped underlying fine kernel coordinates.
The label map need not be injective or surjective, and no scalar-linearity or
compatibility between the coefficient semirings is required. -/
theorem linearEquivPiKer_apply_map_fiberwise
    (υ : B →+* Module.End T N) (b : J → B)
    (hcop' : Pairwise fun j k ↦ IsCoprime (b j) (b k))
    (hAnn' : υ (∏ j, b j) = 0)
    (q : ι → J) (h : M →+ N)
    (hh : ∀ j, Function.Semiconj h (τ (∏ i with q i = j, a i)) (υ (b j)))
    (x : M) (j : J) :
    (υ.linearEquivPiKer b hcop' hAnn' (h x) j : N) =
      ∑ i with q i = j, h (τ.linearEquivPiKer a hcop hAnn x i : M) := by
  simpa only [linearEquivPiKer_apply, LinearMap.sum_apply, map_sum] using
    (τ.semiconj_sum_kerProjector a hcop hAnn υ b hcop' hAnn' q h hh j x).symm

end Fiberwise

/-- An additive map intertwining the labelled annihilating operators intertwines the
canonical kernel projectors. The coefficient and scalar semirings on the two sides
are independent; compatibility with other represented elements is not required. -/
theorem semiconj_kerProjector
    (υ : B →+* Module.End T N) (b : ι → B)
    (hcop' : Pairwise fun i j ↦ IsCoprime (b i) (b j))
    (hAnn' : υ (∏ i, b i) = 0)
    (h : M →+ N) (hh : ∀ i, Function.Semiconj h (τ (a i)) (υ (b i))) :
    ∀ i, Function.Semiconj h
      (τ.kerProjector a hcop hAnn i) (υ.kerProjector b hcop' hAnn' i) := by
  classical
  have hfid (j : ι) : Finset.univ.filter (fun k : ι ↦ k = j) = {j} := by
    ext k
    simp
  intro i x
  have hp := τ.semiconj_sum_kerProjector a hcop hAnn υ b hcop' hAnn' _root_.id h
    (by
      intro j y
      change h (τ (∏ k with k = j, a k) y) = υ (b j) (h y)
      rw [hfid, Finset.prod_singleton]
      exact hh j y) i x
  change h ((∑ k with k = i, τ.kerProjector a hcop hAnn k : Module.End R M) x) =
    υ.kerProjector b hcop' hAnn' i (h x) at hp
  rw [hfid, Finset.sum_singleton] at hp
  exact hp

/-- Kernel-equivalence coordinates commute, on their underlying values, with an
additive map intertwining the labelled annihilating operators. No scalar-linearity
or compatibility between the coefficient semirings is required. -/
theorem linearEquivPiKer_apply_map
    (υ : B →+* Module.End T N) (b : ι → B)
    (hcop' : Pairwise fun i j ↦ IsCoprime (b i) (b j))
    (hAnn' : υ (∏ i, b i) = 0)
    (h : M →+ N) (hh : ∀ i, Function.Semiconj h (τ (a i)) (υ (b i)))
    (x : M) (i : ι) :
    (υ.linearEquivPiKer b hcop' hAnn' (h x) i : N) =
      h (τ.linearEquivPiKer a hcop hAnn x i : M) := by
  simpa only [linearEquivPiKer_apply] using
    (τ.semiconj_kerProjector a hcop hAnn υ b hcop' hAnn' h hh i x).symm

end Naturality

end RingHom

namespace Polynomial

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {S : Type uA} [CommSemiring S]
variable {ι : Type uI} [Fintype ι]

/-- Coprime polynomial kernel decomposition with relative coefficients. Only the
coefficient image must commute with `f`; no algebra structure on all endomorphisms
is required. The only annihilation premise concerns the evaluated product. -/
noncomputable def linearEquivPiKer (σ : S →+* Module.End R M) (f : Module.End R M)
    (hcomm : ∀ s, Commute (σ s) f) (p : ι → S[X])
    (hcop : Pairwise fun i j ↦ IsCoprime (p i) (p j))
    (hAnn : eval₂RingHom' σ f hcomm (∏ i, p i) = 0) :
    M ≃ₗ[R] (∀ i, LinearMap.ker (eval₂RingHom' σ f hcomm (p i))) :=
  (eval₂RingHom' σ f hcomm).linearEquivPiKer p hcop hAnn

/-- A polynomial coordinate is the general represented-semiring kernel projector. -/
@[simp]
theorem linearEquivPiKer_apply
    (σ : S →+* Module.End R M) (f : Module.End R M)
    (hcomm : ∀ s, Commute (σ s) f) (p : ι → S[X])
    (hcop : Pairwise fun i j ↦ IsCoprime (p i) (p j))
    (hAnn : eval₂RingHom' σ f hcomm (∏ i, p i) = 0) (x : M) (i : ι) :
    (linearEquivPiKer σ f hcomm p hcop hAnn x i : M) =
      (eval₂RingHom' σ f hcomm).kerProjector p hcop hAnn i x := by
  exact RingHom.linearEquivPiKer_apply _ _ _ _ x i

/-- The inverse polynomial kernel equivalence sums the kernel inclusions. -/
@[simp]
theorem linearEquivPiKer_symm_apply
    (σ : S →+* Module.End R M) (f : Module.End R M)
    (hcomm : ∀ s, Commute (σ s) f) (p : ι → S[X])
    (hcop : Pairwise fun i j ↦ IsCoprime (p i) (p j))
    (hAnn : eval₂RingHom' σ f hcomm (∏ i, p i) = 0)
    (x : ∀ i, LinearMap.ker (eval₂RingHom' σ f hcomm (p i))) :
    (linearEquivPiKer σ f hcomm p hcop hAnn).symm x = ∑ i, (x i : M) := by
  exact RingHom.linearEquivPiKer_symm_apply _ _ _ _ x

end Polynomial

namespace Submodule

variable {R : Type uR} [CommSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {ι : Type uI}

/-- Scalar product-torsion decomposes as the product of the individual torsion
submodules, without additive inverses. This uses the existing scalar representation,
and the kernels are definitionally `Submodule.torsionBy`. -/
noncomputable def linearEquivPiTorsionBy (s : Finset ι) (a : ι → R)
    (hcop : (s : Set ι).Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hM : Module.IsTorsionBy R M (∏ i ∈ s, a i)) :
    M ≃ₗ[R] (∀ i : s, torsionBy R M (a i)) :=
  (Module.toModuleEnd R M).linearEquivPiKer (fun i : s ↦ a i)
    (by
      intro i j hij
      exact hcop i.property j.property (fun h ↦ hij (Subtype.ext h)))
    (by
      apply LinearMap.ext
      intro x
      change (∏ i : s, a i) • x = 0
      rw [Finset.prod_coe_sort]
      exact @hM x)

/-- Every whole complementary-product Bézout partition computes the scalar
decomposition coordinates by scalar multiplication. -/
theorem linearEquivPiTorsionBy_apply_of_bezout [DecidableEq ι]
    (s : Finset ι) (a : ι → R)
    (hcop : (s : Set ι).Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hM : Module.IsTorsionBy R M (∏ i ∈ s, a i)) (μ : s → R)
    (hμ : (∑ i : s, μ i * ∏ j ∈ {i}ᶜ, a j) = 1) (x : M) (i : s) :
    (linearEquivPiTorsionBy s a hcop hM x i : M) =
      (μ i * ∏ j ∈ {i}ᶜ, a j) • x := by
  exact (RingHom.linearEquivPiKer_apply (Module.toModuleEnd R M)
    (fun j : s ↦ a j) _ _ x i).trans
    (LinearMap.congr_fun
      (RingHom.kerProjector_eq_of_bezout (Module.toModuleEnd R M)
        (fun j : s ↦ a j) _ _ μ hμ i) x)

/-- The scalar torsion equivalence reconstructs an element by summing its components. -/
@[simp]
theorem linearEquivPiTorsionBy_symm_apply (s : Finset ι) (a : ι → R)
    (hcop : (s : Set ι).Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hM : Module.IsTorsionBy R M (∏ i ∈ s, a i))
    (x : ∀ i : s, torsionBy R M (a i)) :
    (linearEquivPiTorsionBy s a hcop hM).symm x = ∑ i : s, (x i : M) := by
  exact RingHom.linearEquivPiKer_symm_apply (Module.toModuleEnd R M) (fun i : s ↦ a i) _ _ x

end Submodule

namespace Submodule

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {ι : Type uI} [DecidableEq ι]

/-- Under the hypotheses of Mathlib's `Submodule.torsionBy_isInternal`, the inverse
scalar kernel equivalence, restricted to the direct sum, is exactly the canonical map
whose bijectivity is supplied directly by that theorem. This compares maps and components,
rather than proofs of internality. The semiring kernel construction generalizes that
commutative-ring, additive-group result. -/
theorem linearEquivPiTorsionBy_symm_comp_coeFnLinearMap (s : Finset ι) (a : ι → R)
    (hcop : (s : Set ι).Pairwise fun i j ↦ IsCoprime (a i) (a j))
    (hM : Module.IsTorsionBy R M (∏ i ∈ s, a i)) :
    ((linearEquivPiTorsionBy s a hcop hM).symm.toLinearMap.comp
        (DirectSum.coeFnLinearMap R) =
      DirectSum.coeLinearMap (fun i : s ↦ torsionBy R M (a i))) ∧
      Function.Bijective (DirectSum.coeLinearMap (fun i : s ↦ torsionBy R M (a i))) :=
  ⟨by
    exact RingHom.linearEquivPiKer_symm_comp_coeFnLinearMap _ _ _ _,
    torsionBy_isInternal hcop hM⟩

end Submodule
