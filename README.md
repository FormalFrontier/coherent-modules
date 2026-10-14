# coherent-modules

Reusable Lean library for coherent modules and rings, finite presentation,
localization, closure constructions, finite square-zero extensions, left
Noetherianity of square-zero extensions, and ideal-to-module transfer.
Import `CoherentModules` for the mathematical library; test modules are separate.
See the [mathematical guide](docs/Guide.md),
the [historical API reference](docs/API.md) and its [provenance](docs/README.md),
and [credits](docs/CREDITS.md). The finite-idealization declarations are linked
to their current source below. Original project contributions are distributed
under [Apache-2.0](LICENSE).

Authors: Formal Frontier Agents

## Headline results

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
