# coherent-modules

Reusable Lean theory of coherent rings and modules, finite presentation,
localization and closure constructions.

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). Review evidence is revision-specific; the historical
development records below do not certify later artifacts or complete source
formalization. Release tags are deferred. Read the [mathematical guide](docs/Guide.md), complete
[native API reference](docs/API.md), [generation instructions](docs/README.md) and
[contributor/provenance record](docs/CREDITS.md).

## Mathematical scope

A module is coherent when it is finitely generated and each finitely generated
submodule is finitely presented. The library characterizes coherence by finitely
generated kernels of maps from finite-rank free modules and proves closure under
finitely generated submodules, linear equivalences, finite products, kernels,
quotients by finitely generated submodules, cokernels and extensions.

Over a coherent ring, finite presentation is equivalent to coherence. Kernels of
maps between finitely presented modules are then finitely presented. A five-term
sequence exact at its three middle terms gives finite presentation of the middle
module when the first module is finite and the second, fourth and fifth are
finitely presented; no exactness at either endpoint is required.

Over a commutative ring, localization preserves coherence, and coherence descends
from localizations away from a set spanning the unit ideal. Linear maps from a
finitely presented module to a coherent module form a coherent module. The tensor
product of a finitely presented left factor and a coherent right factor is also
coherent. The Hom and tensor results are theorems, not automatic instances, and
do not assume that the base ring itself is coherent or Noetherian.

The library constructs the abelian full subcategory `CoherentModuleCat R` of
`ModuleCat R`. It also defines universally coherent commutative rings with an
explicit target-algebra universe and proves the Noetherian case.

The foundation, finite-presentation and category APIs retain arbitrary `Ring`;
the localization, Hom, tensor and universal-coherence interfaces use `CommRing`.
Module carrier universes are independent where stated. In
`IsUniversallyCoherent.{u, v} R`, `u` is the base-ring universe and `v` is the
target-algebra universe; coherence of the base itself uses the `v = u` instance.
Zero rings/modules and empty/rank-zero finite free modules are not excluded.
Always consult the declaration type for its exact assumptions.

## Public entry points

Use `import CoherentModules` for the full public API, or import a subject leaf.
The root re-exports all seven leaves; examples are kept in a separate test library.

| Leaf (prefix `CoherentModules.`) | Representative public API |
| --- | --- |
| `Basic` | `Module.IsCoherent`, `IsCoherentRing`, `Module.IsCoherent.iff_finite_and_fg_ker`, `Module.IsCoherent.of_exact` |
| `FinitePresentation` | `Module.FinitePresentation.isCoherent`, `Module.isCoherent_iff_finitePresentation`, `Module.FinitePresentation.ker`, `Module.FinitePresentation.of_exact_five` |
| `Hom` | `Module.IsCoherent.linearMap` |
| `Localization` | `Module.IsCoherent.of_isLocalizedModule`, `Module.IsCoherent.of_localizationSpan'` and their canonical specializations |
| `ModuleCat` | `ModuleCat.isCoherent`, `CoherentModuleCat` and the inherited abelian structure |
| `TensorProduct` | `Module.IsCoherent.tensorProduct` |
| `UniversallyCoherent` | `IsUniversallyCoherent`, `IsUniversallyCoherent.isCoherentRing_of_algEquiv` |

For example, given `[CommRing R]`, modules `M` and `N`,
`[Module.FinitePresentation R M]` and `[Module.IsCoherent R N]`, use
`Module.IsCoherent.linearMap` for `M →ₗ[R] N` or
`Module.IsCoherent.tensorProduct` for `M ⊗[R] N`. No additional coherence instance
for `R` is needed. The tracked examples exercise these exact interfaces as well as
degenerate cases. They use stable private declarations so their proof bodies can
be checked without becoming a second public API.

## Build and checks

Use elan with the exact `lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`.
The direct mathlib revision is
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; `lake-manifest.json` pins the complete
nine-package dependency graph. No other Formal Frontier deliverable or source
research checkout is required. The Lake package version is not an official tag.

Fetch the matching cache successfully before building; a failed fetch must not
silently become a full mathlib source rebuild:

```sh
lake exe cache get
lake --wfail build
```

The default build includes both `CoherentModules` and `CoherentModulesTest`.
The latter reaches all nine tracked test/audit files. They can also be built with
`lake --wfail build CoherentModulesTest`. Individual files can be checked with,
for example, `lake env lean -DwarningAsError=true CoherentModulesTest/Basic.lean`.

The historical public audit selects 39 declarations, including one imported
category construction. Named example checks supplement that list; neither is a
complete inventory of public, private or generated declarations. A successful
build or `-T0` elaboration is not a compatible separate stored-body proof recheck.
Exact candidate evidence must establish what was actually run. The API reference
covers all 17 modules and 54 native display sites, including classes, constructors
and fields; it is distinct from a complete private/generated proof inventory.
Full release proof/rights review and measured build/check resource evidence remain
separate requirements, not passes inferred from these commands. See the guide
for performance expectations and limits.

## References, credit and development status

These are classical coherent-ring/module constructions, implemented using Lean and
mathlib's native modules, finite presentations, exact sequences, localizations,
tensor products and full subcategories. Background includes Kazuhiro Fujiwara and
Fumiharu Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). No source PDF or substantial
source excerpt is bundled. Detailed passage correspondence and coverage belong
to source-metadata repositories, not to this library's public interface.

Formal Frontier AI agents developed and reviewed this library. Anchor contributed
the original coherent-module foundation, kernel closure and universal-coherence
units and coordinates integration. Attributed Worker B executions contributed the
finite-free characterization, quotient/category construction and exact-five
criterion. Attributed Worker A executions contributed localization/descent, the
finite-presentation bridge, extension closure, Hom and tensor closure. Later
assembly retains and adapts those contributions; collective credit does not erase
the original contributor record or assert legal copyright ownership.

The exact original candidates and execution identities are preserved in the
standalone [credits](docs/CREDITS.md); detailed development review records are
retained separately by the project.
Worker identities denote separate AI executions, not human authors or reviewers.
No human peer review, mathematical novelty or source-author endorsement is claimed.

Accepted development revision `91e1a1e8881ef55c045b3a5eb5285875be21a00d` includes
those units and the independently reviewed module/example/readiness assembly
(review 2994, acceptance 40452, integration 40468 and main verification 40474).
All 17 Lean files and three dependency/configuration inputs are unchanged here.
The recorded development review did not assess the later documentation/license/
metadata assembly. Full-release acceptance must bind the exact artifact and its
applicable independent review; public-API semantics, complete proof integrity,
rights/provenance, documentation and promotion are separate decisions. Historical
unsupported project-owner labels were corrected with their origins recorded;
history and actual contributor credit are preserved, not replaced by another owner.

See `formalization.yaml` for the bounded project self-report. Schema validity is
not mathematical, legal or release certification.
