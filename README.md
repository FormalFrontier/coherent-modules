# coherent-modules

Reusable Lean library for coherent modules and rings, finite presentation,
localization, closure constructions, finite square-zero extensions, left
Noetherianity of square-zero extensions, ideal-to-module transfer, and
finite-generation ascent under pointwise unimodular clearing and Noetherian
ascent under left-invertible scalar clearing for semilinear maps.
Import `CoherentModules` for the mathematical library; test modules are separate.
See the [mathematical guide](docs/Guide.md),
the [historical API reference](docs/API.md) and its [provenance](docs/README.md),
and [credits](docs/CREDITS.md). The finite-idealization declarations are linked
to their current source below. Original project contributions are distributed
under [Apache-2.0](LICENSE).

Authors: Formal Frontier Agents

## Headline results

- **Finite generation under pointwise unimodular clearing.** For arbitrary,
  possibly noncommutative semirings `R`, `S` and `f : M →ₛₗ[φ] N` between
  additive commutative left semimodules,
  [`Submodule.fg_of_fg_comap_of_one_mem_span_smul_mem_range`](CoherentModules/Algebra/Module/SpanRank.lean)
  proves an `S`-submodule `P` finitely generated if `P.comap f` is finitely
  generated over `R` and, for every `n ∈ P`, the clearers
  `{a : S | ∃ m : M, f m = a • n}` generate the unit **left** ideal.
  The companion `span_image_comap_eq_of_one_mem_span_smul_mem_range` identifies
  `P` with the target-scalar span of its comap image without any finite-generation
  premise. The existing single-left-inverse and unit-clearing criteria remain
  specializations. The four universes are independent; neither Noetherianity
  nor surjectivity of `φ` or `f` is required.
- **Semilinear Noetherian ascent.** For arbitrary semirings `R`, `S`, additive
  commutative semimodules `M`, `N` and `f : M →ₛₗ[φ] N`,
  [`isNoetherian_of_left_inv_smul_mem_range`](CoherentModules/RingTheory/Noetherian.lean)
  transfers `IsNoetherian R M` to `IsNoetherian S N` if each `n` admits
  `m, a, b` with `b * a = 1` and `f m = a • n`. The four universes are
  independent; neither `φ` nor `f` must be surjective. The
  `isNoetherian_of_unit_smul_mem_range` corollary retains the familiar
  unit-clearing hypothesis, while `isNoetherian_of_surjective_semilinear`
  requires only function-surjectivity of `f`.
- **Coherent modules and kernels.** [`Module.IsCoherent`](CoherentModules/Basic.lean)
  means finite generation together with finite presentation of every finitely
  generated submodule. [`Module.IsCoherent.iff_finite_and_fg_ker`](CoherentModules/Basic.lean)
  characterizes this by finitely generated kernels of *all* linear maps from
  finite-rank free modules, including rank zero. The same leaf proves closure
  under finitely generated submodules, finite products, kernels and cokernels,
  quotients by finitely generated submodules, and extensions (with the stated
  exactness and endpoint conditions).
- **Finite presentation over coherent rings.** [`Module.isCoherent_iff_finitePresentation`](CoherentModules/FinitePresentation.lean)
  identifies the two properties over an `IsCoherentRing R`, yielding finite
  presentation of kernels between finitely presented modules. The
  [`of_exact_five` criterion](CoherentModules/FinitePresentation.lean) gives finite
  presentation of `M₃` in `M₁ → M₂ → M₃ → M₄ → M₅` when the sequence is exact
  at `M₂`, `M₃`, `M₄`, `M₁` is finite, and `M₂`, `M₄`, `M₅` are finitely
  presented. It requires neither endpoint injectivity nor surjectivity.
- **Localization and descent.** [`of_isLocalizedModule`](CoherentModules/Localization.lean)
  transports coherence along an arbitrary commutative-ring/module localization
  realized by its universal property, not a surjective map. The
  [`of_localizationSpan'` theorem](CoherentModules/Localization.lean) descends
  coherence from localizations away from a family whose ideal span is `⊤`.
- **Hom, tensor, and categories.** [`linearMap`](CoherentModules/Hom.lean) and
  [`tensorProduct`](CoherentModules/TensorProduct.lean) make the Hom module and
  tensor product coherent when the first argument is finitely presented and
  the second coherent. Neither theorem assumes a coherent or Noetherian base;
  they are not global instances. [`CoherentModuleCat`](CoherentModules/ModuleCat.lean)
  is a transparent full subcategory with abelian structure obtained through
  generic category constructions.
- **Finite-module tensor zero detection.** For an arbitrary additive commutative
  `R`-module `P` over a `CommRing R`,
  [`Module.forall_maximal_smul_top_ne_top_iff_forall_finite_tensorProduct`](CoherentModules/LinearAlgebra/TensorProduct/FiniteDetection.lean)
  characterizes zero-object detection on all finite modules by
  `m • (⊤ : Submodule R P) ≠ ⊤` for every maximal ideal `m`.
  [`Module.subsingleton_tensorProduct_iff_of_finite`](CoherentModules/LinearAlgebra/TensorProduct/FiniteDetection.lean)
  gives `Subsingleton (P ⊗[R] M) ↔ Subsingleton M` for a single finite module
  in an independent universe. No flatness, faithfulness or finiteness of `P`
  is required. This detects zero objects, not zero maps or isomorphisms. The
  [clients](CoherentModulesTest/LinearAlgebra/TensorProduct/FiniteDetection.lean)
  recover the finite faithfully-flat and local residue-field criteria and use
  a countable direct sum of residue fields.
- **Ideal action on finite coefficients.** For an FG submodule `N` of an arbitrary
  additive commutative module over a `CommRing R`,
  [`Submodule.FG.ideal_smul_eq_self_iff_sup_annihilator_eq_top`](CoherentModules/RingTheory/Nakayama.lean)
  says `I • N = N ↔ I ⊔ N.annihilator = ⊤` for every ideal `I`. For finite `P`,
  [`Module.forall_maximal_smul_top_ne_top_iff_annihilator_le_jacobson`](CoherentModules/RingTheory/Nakayama.lean)
  characterizes proper image under every maximal ideal by
  `Module.annihilator R P ≤ Ideal.jacobson ⊥`, with no flatness or faithful-action
  assumption. The [clients](CoherentModulesTest/RingTheory/Nakayama.lean) recover
  relative Jacobson properness and supply the finite tensor-detection input.
- **Faithfully flat tensor products.** Over a `CommRing R`, for additive
  commutative groups `C` and `D` with `R`-module structures,
  [`Module.FaithfullyFlat.tensorProduct_iff`](CoherentModules/RingTheory/Flat/TensorProduct.lean)
  says that `C ⊗[R] D` is faithfully flat over `R` if and only if both `C` and
  `D` are faithfully flat over `R`. The ring and the two module universes are
  independent; no finiteness, projectivity or nontriviality assumption is needed.
- **Faithfully flat dependent direct sums.** For arbitrary families of additive
  commutative groups with module structures over a `CommRing R`,
  [`Module.FaithfullyFlat.directSum_iff`](CoherentModules/RingTheory/Flat/DirectSum.lean)
  characterizes faithful flatness of the direct sum by flatness of every
  component and a nontrivial quotient-tensor fiber in some component for each
  proper ideal of `R`. The detecting component may depend on the ideal; the
  components need not individually be faithfully flat. The ring, index and
  carrier universes are independent, and empty indexing types are allowed.
  One faithfully flat component is sufficient when every component is flat.
- **Finitely generated ideals and dependent products.** Over a `CommSemiring R`,
  [`Submodule.smul_pi_of_fg`](CoherentModules/LinearAlgebra/Pi.lean) says that
  multiplication by a finitely generated ideal commutes with the full dependent
  product of submodules of additive commutative `R`-modules. The index type is
  arbitrary, including empty, and the semiring, index and carrier universes are
  independent.
- **Faithful flatness after base change covering maximal ideals.** For commutative
  rings `R` and `S` with an `R`-algebra structure on `S`, suppose every maximal
  ideal `m` of `R` satisfies `m.map (algebraMap R S) ≠ ⊤`. For any additive
  commutative group `M` with an `R`-module structure,
  [`Module.FaithfullyFlat.iff_flat_and_baseChange_of_map_maximal_ne_top`](CoherentModules/RingTheory/Flat/FaithfullyFlat.lean)
  characterizes faithful flatness over `R` by **original** flatness `Module.Flat R M`
  and faithful flatness over `S` of `S ⊗[R] M`, with the canonical left tensor-factor
  action. The three universes are independent. No flatness of `S` over `R`,
  surjectivity, algebra structure on `M`, finiteness, Noetherianity, localness,
  topology or completion is assumed. For `I ≤ Ideal.jacobson (⊥ : Ideal R)`,
  [`Module.FaithfullyFlat.iff_flat_and_baseChange_of_le_jacobson`](CoherentModules/RingTheory/Flat/FaithfullyFlat.lean)
  specializes this to the canonical quotient `R ⧸ I`. For commutative
  `R`-algebras `S`,
  [`Module.FaithfullyFlat.iff_flat_and_quotient_of_le_jacobson`](CoherentModules/RingTheory/Flat/FaithfullyFlat.lean)
  gives the equivalent formulation using the canonical quotient algebra
  `R ⧸ I → S ⧸ I.map (algebraMap R S)`. Conversely,
  [`Algebra.map_maximal_ne_top_iff_forall_faithfullyFlat_baseChange`](CoherentModules/RingTheory/Flat/BaseChange.lean)
  characterizes the maximal-ideal hypothesis itself: it holds **if and only if**
  scalar extension preserves and reflects faithful flatness for every originally
  flat `R`-module in `Type (max u w)`, where `R : Type u` and `w` is arbitrary.
  The universe of `S` remains independent. The converse uses the direct sum of
  principal localizations indexed by all elements of a maximal ideal, without
  assuming that ideal is finitely generated. The
  [quotient client](CoherentModulesTest/RingTheory/Flat/FaithfullyFlat.lean)
  applies this corollary to the nonsurjective rank-two diagonal over `ZMod 4`
  with the proper nonzero square-zero ideal `(2)`. Its inputs are obtained
  independently from basis-derived faithful flatness.
- **Faithful flatness of unital algebras.** For a `CommRing R` and a unital
  `R`-algebra `A` whose underlying ring may be noncommutative,
  [`Module.FaithfullyFlat.algebra_iff_flat_and_fg_proper_ideal`](CoherentModules/RingTheory/Flat/FaithfullyFlat.lean)
  characterizes faithful flatness by flatness and
  `I • (⊤ : Submodule R A) ≠ ⊤` for every finitely generated proper ideal `I`.
  The algebra structure is material; this finitely generated ideal criterion
  is not asserted for arbitrary modules.
- **Faithfully flat products of algebras.** Over a `CommRing R`, for an arbitrary
  dependent family of unital, possibly noncommutative `R`-algebras `A i`,
  [`Module.FaithfullyFlat.pi_algebra_iff`](CoherentModules/RingTheory/Flat/Pi.lean)
  characterizes faithful flatness of `Π i, A i` by flatness of the **whole
  product** and a nontrivial fiber `(R ⧸ I) ⊗[R] A i` in some component for
  every finitely generated proper ideal `I`. The detecting component may depend
  on the ideal. Componentwise flatness cannot replace whole-product flatness,
  and the components need not individually be faithfully flat. The ring, index
  and carrier universes are independent, and empty products are allowed.
- **Products of localizations at submonoids.** For a `CommRing R`, arbitrary
  submonoids `S i` and commutative `R`-algebras `A i` realizing the localizations
  at `S i`,
  [`Module.FaithfullyFlat.pi_localization_iff`](CoherentModules/RingTheory/Flat/Localization.lean)
  characterizes faithful flatness of `Π i, A i` by flatness of the **whole
  product** and, for every finitely generated proper ideal `I`, disjointness
  of `I` from some `S i`. These are products with the common diagonal `R`-action;
  neither finite nor nonempty indexing is required, and zero rings are allowed.
- **Families of principal localizations.** For a `CommRing R` and any family
  `s : ι → R`,
  [`Module.FaithfullyFlat.directSum_away_iff`](CoherentModules/RingTheory/Flat/Localization.lean)
  characterizes faithful flatness of `⨁ i, Localization.Away (s i)` by
  `Ideal.span (Set.range s) = ⊤`, without finite or nonempty indexing.
  For **finite** index types,
  [`Module.FaithfullyFlat.pi_away_iff`](CoherentModules/RingTheory/Flat/Localization.lean)
  gives the same unit-span criterion for `Π i, Localization.Away (s i)`.
  The localizations need not individually be faithfully flat; zero rings and
  independent ring and index universes are allowed. The finite-index hypothesis
  for the product unit-span criterion is essential: the
  [coordinate-idempotent product](CoherentModulesTest/RingTheory/Flat/LocalizationProductInfinite.lean)
  is faithfully flat although its generators span a proper ideal. The
  [ideal-detection consequences](CoherentModulesTest/RingTheory/Flat/LocalizationProductCriteria.lean)
  show that this ideal is not finitely generated.
- **Universal coherence.** [`IsUniversallyCoherent`](CoherentModules/UniversallyCoherent.lean)
  asserts coherence for finitely presented commutative algebras in an independently
  chosen target universe; the library derives base coherence at `v = u` and
  supplies the Noetherian case.
- **Square-zero kernels and projection base change.** For a commutative semiring
  `R` and an additive commutative `R`-module `M`,
  [`TrivSqZeroExt.kerIdealLinearEquiv`](CoherentModules/Algebra/TrivSqZeroExt/Finite.lean)
  identifies the projection kernel with `M`. If `M` is finite over `R`,
  [`kerIdeal_finite`](CoherentModules/Algebra/TrivSqZeroExt/Finite.lean) makes the
  kernel finite over the **whole extension**.
  [`kerIdealBaseChange`](CoherentModules/Algebra/TrivSqZeroExt/Finite.lean)
  identifies the projection-base-changed kernel with `M` **without** a finiteness
  assumption; its pure-tensor and inverse formulas are simp lemmas.
- **Left Noetherian square-zero extensions.** For a possibly noncommutative
  `Ring R` and an `AddCommMonoid M` with commuting left and right `R`-module
  actions, [`TrivSqZeroExt.isNoetherianRing_iff`](CoherentModules/Algebra/TrivSqZeroExt/Noetherian.lean)
  characterizes `IsNoetherianRing (TrivSqZeroExt R M)` by
  `IsNoetherianRing R ∧ Module.Finite R M`. Finiteness here is as a **left**
  `R`-module. The companion `TrivSqZeroExt.isNoetherianRing_iff_isNoetherian`
  replaces `Module.Finite R M` by `IsNoetherian R M`. Centrality is not required,
  and the two carrier universes are independent.
- **Finite-type ideal/module transfer.** Over a commutative base ring,
  [`Ideal.ideal_property_iff_module_property`](CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean)
  equates a property on all finitely generated ideals with one on all finite
  modules over finite-type algebras. The property must be invariant under
  compatible algebra/module isomorphisms and descend along **every** compatible
  surjective square-zero algebra map for finite source modules. The base universe
  is independent of the common algebra/module universe. Finite type does not
  mean module-finite over the base, and arbitrary ideals need not be finitely
  generated.

The foundation, finite-presentation and category results allow arbitrary `Ring`;
localization, Hom, tensor and universal coherence use `CommRing`. The square-zero
kernel and base-change results use `CommSemiring` and `AddCommMonoid`; the
square-zero Noetherian criterion allows `Ring` and `AddCommMonoid` with commuting
bimodule actions. The predicate transfer uses `CommRing` and `AddCommGroup`.
The ideal/product identity uses `CommSemiring` and `AddCommMonoid`; the
faithful-flatness criteria use `CommRing` and require no coherence or projectivity
assumption. Module carrier universes are independent where stated.
Zero rings/modules, empty indexing sets and rank-zero finite free
modules are not excluded. Consult the linked source statements and
[guide](docs/Guide.md) for exact hypotheses. This is not a coherent-sheaf theory
or a claim to formalize an entire source.

## Scalar clearing and Noetherianity

For a semilinear map `f : M →ₛₗ[φ] N` over arbitrary semirings, suppose each
`n : N` has witnesses `m : M` and `a, b : S` with `b * a = 1` and
`f m = a • n`. Then
[`Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range`](CoherentModules/RingTheory/Noetherian.lean)
shows that comap reflects submodule order. Mathlib's ascending-chain criterion
therefore transfers Noetherianity from `M` over `R` to `N` over `S`.
Recovery uses `b • f m = (b * a) • n = n`; a right inverse alone would not
justify this calculation on a left semimodule. No commutativity, additive
inverses, nontriviality, scalar tower or additional source action on `N` is
assumed. The witnesses may depend on `n`.

Clearing by a unit `u` specializes this with `a = ↑u`, `b = ↑(u⁻¹)`.
The function-surjective corollary uses the unit `1`. When `φ` is surjective,
`LinearMap.range_eq_top_iff_left_inv_smul_mem_range` identifies scalar clearing
with `LinearMap.range f = ⊤`. The
[range bridge](CoherentModulesTest/RingTheory/Noetherian.lean) then derives ascent
from Mathlib's `isNoetherian_of_surjective` under its scalar-surjectivity class.
That class is not a hypothesis of the new ascent theorems.

For semirings `R` and `S` and a homomorphism `f : R →+* S`, suppose every
`s : S` admits a unit `u : Sˣ` such that `(u : S) * s` belongs to the image of `f`.
Then [`Ideal.map_comap_eq_of_unit_mul_mem_range`](CoherentModules/RingTheory/Noetherian.lean)
says that every left ideal of `S` is the extension of its contraction to `R`.
Consequently [`isNoetherianRing_of_unit_mul_mem_range`](CoherentModules/RingTheory/Noetherian.lean)
transfers left Noetherianity from `R` to `S` as the regular-semimodule
specialization of unit clearing.
The source and target universes are independent.

The units need not be central or arise from the source. No commutativity,
injectivity or two-sidedness assumption is needed.
`RingHom.exists_unit_mul_mem_range_of_surjective` supplies the hypothesis for
surjective homomorphisms by taking `u = 1`, recovering the usual surjective
ideal and Noetherian results.

## Using the library

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "coherent-modules"
git = "https://github.com/FormalFrontier/coherent-modules.git"
rev = "main"
```

GitHub `main` tracks reviewed releases. Lake resolves its commit when you first
add or update the dependency; `lake-manifest.json` keeps that revision until the
next update. To pin a particular release, replace `main` with its full published
commit. Dependencies between deliverable libraries should use full release pins.

```lean
import CoherentModules
```

## Use and verification

### API and focused imports

For `[CommRing R]`, `[Module.FinitePresentation R M]` and
`[Module.IsCoherent R N]`, apply `Module.IsCoherent.linearMap` to `M →ₗ[R] N`
or `Module.IsCoherent.tensorProduct` to `M ⊗[R] N`. The
[Hom](CoherentModulesTest/Hom.lean), [tensor](CoherentModulesTest/TensorProduct.lean),
[category](CoherentModulesTest/ModuleCat.lean) and
[finite-presentation](CoherentModulesTest/FinitePresentationZero.lean) clients
include degenerate cases. For the square-zero results, import
`CoherentModules.Algebra.TrivSqZeroExt.Finite`; the ideal/module theorem is in
`CoherentModules.RingTheory.Ideal.FiniteModuleTransfer`. Use
`open scoped TrivSqZeroExt` for the canonical opposite and central scalar actions.
The [finite-idealization client](CoherentModulesTest/Algebra/TrivSqZeroExt/Finite.lean)
exercises finite nonfree torsion, zero modules, the semiring base-change formulas,
and independently verified invariance and descent premises for predicate transfer.
For the left Noetherian criterion, import
`CoherentModules.Algebra.TrivSqZeroExt.Noetherian`; its two equivalences also
apply to noncommutative coefficient rings and noncentral bimodules. For the
faithful-flatness criterion, import `CoherentModules.RingTheory.Flat.TensorProduct`;
the [tensor-product client](CoherentModulesTest/RingTheory/Flat/TensorProduct.lean)
uses nonfinite free abelian groups in independent universes and an empty-index
boundary.

For a family of principal localizations, import
`CoherentModules.RingTheory.Flat.Localization` and apply
`Module.FaithfullyFlat.directSum_away_iff R s`, or
`Module.FaithfullyFlat.pi_away_iff R s` for finite products. The
[integer localization examples](CoherentModulesTest/RingTheory/Flat/Localization.lean)
include a jointly faithfully flat sum whose two components are not faithfully
flat, reciprocal and quotient-tensor values, and empty-index boundaries.
For arbitrary products of localizations at submonoids, use
`Module.FaithfullyFlat.pi_localization_iff R S A`, retaining the whole-product
flatness hypothesis. The
[product-criterion examples](CoherentModulesTest/RingTheory/Flat/LocalizationProductCriteria.lean)
recover the finite product over `ZMod 6` from its jointly faithfully flat direct
sum, prove that the coordinate-idempotent span in `ℕ → ZMod 2` is not finitely
generated, and obtain proper ideal action on a noncommutative matrix product.

For the supporting surjection constructor, import
`CoherentModules.RingTheory.Flat.FaithfullyFlat` and apply
[`Module.FaithfullyFlat.of_surjective`](CoherentModules/RingTheory/Flat/FaithfullyFlat.lean)
to `f : M →ₗ[R] N` and a proof of `Function.Surjective f`. It requires
`[CommRing R]`, `[AddCommGroup M]`, `[AddCommGroup N]`, the two `R`-module
structures, `[Module.Flat R M]` and `[Module.FaithfullyFlat R N]`, and concludes
`Module.FaithfullyFlat R M`. The three universes are independent; no finiteness,
projectivity, splitting or algebra structure is required. Source flatness,
surjectivity and target faithful flatness are all material: faithful scalar
action alone on the target does not suffice. The
[surjection clients](CoherentModulesTest/RingTheory/Flat/FaithfullyFlat.lean)
include a projection onto a nonfinite free abelian group, linear-equivalence
transport, and the rational, empty-index and integer-torsion boundaries.

### Building and checking

The exact `lean-toolchain` is `leanprover/lean4:v4.34.0-rc2`; mathlib is pinned
at `83abb3e776bdefcbc447a1e44d0debe4010039e5`, with the resolved dependency
graph in `lake-manifest.json`. No source-research checkout or other Formal
Frontier deliverable is a dependency. Fetch the matching precompiled mathlib
cache successfully before building; do not silently rebuild mathlib from source
if the fetch fails:

```sh
lake exe cache get
lake --wfail build
```

The default build covers the aggregate and all test modules. For an
individual test, run `lake env lean -DwarningAsError=true CoherentModulesTest/Basic.lean`.
The 38 `#print axioms` checks in
[`CoherentModulesTest/Axioms.lean`](CoherentModulesTest/Axioms.lean) are a
*selected public* list, not a complete transitive axiom audit. A successful build
checks the proofs but does not by itself establish their transitive axiom
closure. Complete verification also checks private and generated declarations
and their dependencies; only `propext`, `Classical.choice` and `Quot.sound`
are allowed. The [guide's measured cost baseline](docs/Guide.md#build-and-audit-resource-baseline)
is historical and qualified, not a present-day resource guarantee.

## References and credit

These classical constructions use Lean and mathlib's modules, exact sequences,
localization, tensor products and categorical infrastructure. The ideal and
product criteria reuse mathlib's dependent submodules, ideal multiples,
quotient-tensor equivalences and `DirectSum.linearEquivFunOnFintype`.
Mathematical background includes Kazuhiro Fujiwara and Fumiharu Kato,
[*Foundations of Rigid Geometry I*](https://arxiv.org/abs/1308.4734v5).
No source PDF or substantial excerpt is bundled; this citation does not assert
complete source correspondence or endorsement. Anchor contributed the original
foundation, kernel closure and universal-coherence units and coordinated
integration; other Formal Frontier AI agents contributed the subsequent
constructions, tests and independent reviews. See [credits](docs/CREDITS.md)
for mathematical and tooling provenance. No legal copyright owner is inferred
from collective author credit.

## Base-change criteria: source and proof approach

The arbitrary-algebra base-change criterion in
`CoherentModules.RingTheory.Flat.FaithfullyFlat` applies when every maximal ideal
extends to a proper ideal, without flatness or surjectivity of the scalar map.
It uses Mathlib's arbitrary faithfully-flat base change and
`TensorProduct.tensorQuotMapSMulEquivTensorQuot`: if a maximal ideal acts with
full image on `M`, the corresponding module quotient vanishes; after tensoring,
the extended ideal acts with full image on `S ⊗[R] M`, contradicting its properness
and the faithful flatness of that module.

The universal converse in `CoherentModules.RingTheory.Flat.BaseChange` shows that
this maximal-ideal condition is necessary for reflection on all originally flat
modules. If a maximal ideal extends to the unit ideal, the direct sum of principal
localizations at all its elements is flat but not faithfully flat over the source.
Mathlib's tensor/direct-sum and localization base-change equivalences identify its
scalar extension with a faithfully flat family of principal localizations over
the target. `ULift` transports this witness to each test universe `max u w`.
The [rational base-change boundary](CoherentModulesTest/RingTheory/Flat/BaseChange.lean)
uses the converse to rule out universal reflection for `ℤ → ℚ`.

Quotienting by an ideal in the Jacobson radical satisfies the maximal-ideal
hypothesis. The module specialization then yields, for commutative algebras,
the canonical quotient criterion. This corollary is an algebraic strengthening
of Fujiwara--Kato, *Foundations of Rigid Geometry I*,
arXiv:1308.4734v5 (2017-02-28), Lemma 0.7.3.6 using Proposition 0.7.3.2(c):
explicit Jacobson containment replaces adic topology and Zariskian packaging,
while original flatness remains a separate necessary hypothesis. It does not
assert formalization of the surrounding adic theory, nor identify the
arbitrary-algebra criterion with the book's statement. The algebra corollary uses
the canonical quotient-algebra/tensor equivalence. These developments are
credited to Mathlib and its authors, including Judith Ludwig, Florent Schaffhauser,
Yunzhou Xie, Jujian Zhang, Antoine Chambert-Loir, Christian Merten, Yi Song, Sihan Su,
Kim Morrison, Johan Commelin and Eric Wieser.
