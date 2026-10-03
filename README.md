# coherent-modules

Reusable Lean library for coherent modules and rings, finite presentation,
localization, closure constructions, finite square-zero extensions, and
ideal-to-module transfer. Import `CoherentModules` for all nine mathematical
leaves; the ten test modules are separate. See the [mathematical guide](docs/Guide.md),
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
kernel and base-change results use `CommSemiring` and `AddCommMonoid`; the predicate
transfer uses `CommRing` and `AddCommGroup`. No coherence or projectivity
assumption is imposed on the new results. Module carrier universes are independent
where stated. Zero rings/modules, empty indexing sets and rank-zero finite free
modules are not excluded. Consult the linked source statements and
[guide](docs/Guide.md) for exact hypotheses. This is not a coherent-sheaf theory
or a claim to formalize an entire source.

## Use and verification

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

The default build covers the aggregate and all ten test modules. For an
individual test, run `lake env lean -DwarningAsError=true CoherentModulesTest/Basic.lean`.
The 38 `#print axioms` checks in
[`CoherentModulesTest/Axioms.lean`](CoherentModulesTest/Axioms.lean) are a
*selected public* list, not a complete transitive axiom audit. Acceptance requires
an applicable successful build and a complete transitive check including private
and generated declarations; only `propext`, `Classical.choice` and `Quot.sound`
are allowed. The [guide's measured cost baseline](docs/Guide.md#build-and-audit-resource-baseline)
is historical and qualified, not a present-day resource guarantee.

## References and credit

These classical constructions use Lean and mathlib's modules, exact sequences,
localization, tensor products and categorical infrastructure. Mathematical
background includes Kazuhiro Fujiwara and Fumiharu Kato,
[*Foundations of Rigid Geometry I*](https://arxiv.org/abs/1308.4734v5).
No source PDF or substantial excerpt is bundled; this citation does not assert
complete source correspondence or endorsement. Anchor contributed the original
foundation, kernel closure and universal-coherence units and coordinated
integration; other Formal Frontier AI agents contributed the subsequent
constructions, tests and independent reviews. See [credits](docs/CREDITS.md)
for mathematical and tooling provenance. No legal copyright owner is inferred
from collective author credit.
