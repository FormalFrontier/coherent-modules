# Using coherent modules

Import `CoherentModules` for the complete library, or one of the seven leaves in
the table below. Its only mathematical dependency is the pinned mathlib. The
[generated API](API.md) supplies native signatures and same-checkout source links;
the linked Lean statements are authoritative about hypotheses and universes.

| Leaf | Purpose and important boundary |
| --- | --- |
| `CoherentModules.Basic` | Coherent modules/rings over an arbitrary `Ring`; finite generation and finite presentation of finitely generated submodules. |
| `CoherentModules.FinitePresentation` | Over a coherent ring, coherence iff finite presentation; exact-five finite-presentation criterion. |
| `CoherentModules.Localization` | Preservation and spanning-family descent over a `CommRing`, for arbitrary localization realizations. |
| `CoherentModules.ModuleCat` | The coherent-object property and transparent abelian full subcategory of `ModuleCat`. |
| `CoherentModules.Hom` | Hom closure over a `CommRing`, with finitely presented source and coherent target. |
| `CoherentModules.TensorProduct` | Tensor closure over a `CommRing`, with finitely presented first factor and coherent second factor. |
| `CoherentModules.UniversallyCoherent` | Coherence of every finitely presented commutative algebra in a specified target universe. |

## Foundation and finite presentation

`Module.IsCoherent R M` packages finite generation of `M` and finite presentation
of every finitely generated submodule. In particular, it gives finite presentation
of `M`. Its finite-free characterization asks for finite generation of kernels of
maps from finite-rank free modules to `M`; the zero-rank case is included.
`IsCoherentRing R` is coherence of `R` as its own module, not a Noetherian condition.

The closure theorems cover finitely generated submodules, linear equivalences,
finite products, kernels between coherent modules, quotients by finitely generated
submodules, cokernels and extensions. They do not assert that every submodule or
every quotient of a coherent module is coherent without the stated finiteness.

Over a coherent ring, finite presentation and coherence are equivalent, so a
kernel between finitely presented modules is finitely presented. The exact-five
criterion concerns `M₁ → M₂ → M₃ → M₄ → M₅`: exactness is required at the three
middle modules; `M₁` is finite and `M₂`, `M₄`, `M₅` are finitely presented. It
concludes finite presentation of `M₃` without endpoint injectivity/surjectivity.

## Localization, Hom and tensor

`Module.IsCoherent.of_isLocalizedModule` uses the ring and module localization
universal properties; it does not require a surjective localization map. The
canonical localization instance and `away` theorem specialize it. Descent uses
localization away from elements of a set whose ideal span is the unit ideal,
including arbitrary realizations in `of_localizationSpan'`.

For `[CommRing R]`, `[Module.FinitePresentation R M]` and
`[Module.IsCoherent R N]`, use `Module.IsCoherent.linearMap` for `M →ₗ[R] N` and
`Module.IsCoherent.tensorProduct` for `M ⊗[R] N`. These are theorems, not global
instances; they require neither a coherent nor a Noetherian base ring. The two
module carrier universes are independent. The tracked
[Hom](../CoherentModulesTest/Hom.lean) and
[tensor](../CoherentModulesTest/TensorProduct.lean) clients demonstrate the exact
applications, including zero/subsingleton boundaries.

## Categories and universal coherence

`ModuleCat.isCoherent` tests coherence of the underlying module. Its closure under
isomorphisms, zero objects, finite products, kernels and cokernels supplies the
generic abelian structure on `CoherentModuleCat R`. The latter remains a transparent
full-subcategory abbreviation; this assembly does not replace its definitional
API or impose a coherent-ring hypothesis. The
[category clients](../CoherentModulesTest/ModuleCat.lean) include reduction checks.

`IsUniversallyCoherent.{u, v} R` quantifies over finitely presented commutative
algebras in `Type v` while `R : Type u`. The target universe is deliberately
independent. Base-ring coherence uses the specialization `v = u`; the algebra-
equivalence theorem transports coherence between suitably equivalent algebras.
The Noetherian instance supplies universal coherence. No nonzero-ring or
nonempty-basis assumption is added.

## Checks, cost and limits

The default Lake targets include the aggregate and all nine `CoherentModulesTest`
modules. Stable private test declarations exercise hypotheses, independent
universes and degenerate cases without creating another exported API. The
historical public axiom list is intentionally not a private/generated proof census.
This docs-only assembly preserves every Lean file and dependency pin from accepted
development revision `91e1a1e8881ef55c045b3a5eb5285875be21a00d`.

This is proof-oriented infrastructure; it promises no efficient executable
algorithm or runtime complexity. Build/check cost depends on the pinned compiler,
dependency cache, machine and selected audit. Exact measured command receipts
belong to release evidence, not a portable performance guarantee. The library
does not yet supply a general coherent-sheaf theory or claim complete coverage
of any mathematical source. See the root README for review and release status.
