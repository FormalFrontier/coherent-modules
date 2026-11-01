# Using coherent modules

Import `CoherentModules` for the complete library, or one of the leaves in
the table below. Its only mathematical dependency is the pinned mathlib. The
[historical generated API](API.md) covers the original seven leaves; follow the
source links below for the square-zero and ideal/module declarations. The Lean
statements are authoritative about hypotheses and universes.

| Leaf | Purpose and important boundary |
| --- | --- |
| `CoherentModules.Basic` | Coherent modules/rings over an arbitrary `Ring`; finite generation and finite presentation of finitely generated submodules. |
| `CoherentModules.FinitePresentation` | Over a coherent ring, coherence iff finite presentation; exact-five finite-presentation criterion. |
| `CoherentModules.Localization` | Preservation and spanning-family descent over a `CommRing`, for arbitrary localization realizations. |
| `CoherentModules.ModuleCat` | The coherent-object property and transparent abelian full subcategory of `ModuleCat`. |
| `CoherentModules.Hom` | Hom closure over a `CommRing`, with finitely presented source and coherent target. |
| `CoherentModules.TensorProduct` | Tensor closure over a `CommRing`, with finitely presented first factor and coherent second factor. |
| `CoherentModules.UniversallyCoherent` | Coherence of every finitely presented commutative algebra in a specified target universe. |
| [`CoherentModules.Algebra.TrivSqZeroExt.Finite`](../CoherentModules/Algebra/TrivSqZeroExt/Finite.lean) | Projection-kernel equivalence, whole-extension kernel finiteness and projection base change over a commutative semiring. |
| [`CoherentModules.Algebra.TrivSqZeroExt.Noetherian`](../CoherentModules/Algebra/TrivSqZeroExt/Noetherian.lean) | Left Noetherianity of a square-zero extension iff the base ring is left Noetherian and the coefficient bimodule is finite on the left. |
| [`CoherentModules.RingTheory.Ideal.FiniteModuleTransfer`](../CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean) | Transfer of isomorphism-invariant, square-zero-descent-stable properties from finite ideals to finite modules over finite-type algebras. |
| [`CoherentModules.RingTheory.Ideal.AdicCompatibility`](../CoherentModules/RingTheory/Ideal/AdicCompatibility.lean) | Finite-submodule adic cofinality (APf), its independent-universe eliminator, and the nilpotent-ideal provider; no ideal-FG or ambient finite-presentation assumption. |
| [`CoherentModules.RingTheory.Filtration`](../CoherentModules/RingTheory/Filtration.lean) | Full Artin–Rees for Noetherian modules over arbitrary commutative rings, and finite-submodule adic cofinality for ideals of Noetherian rings. |

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

## Square-zero extensions and finite modules

For `[CommSemiring R] [AddCommMonoid M] [Module R M]`, the projection kernel of
`TrivSqZeroExt R M` is `R`-linearly equivalent to `M` via
[`TrivSqZeroExt.kerIdealLinearEquiv`](../CoherentModules/Algebra/TrivSqZeroExt/Finite.lean).
The `kerIdealLinearEquiv_apply` and `kerIdealLinearEquiv_symm_apply` simp lemmas
describe its second-coordinate map and inverse `inr`. If `[Module.Finite R M]`,
`TrivSqZeroExt.kerIdeal_finite` makes the kernel finite **as a module over the
whole extension**, not only over `R`. The semiring-level
`TrivSqZeroExt.kerIdealBaseChange` identifies
`R ⊗[TrivSqZeroExt R M] TrivSqZeroExt.kerIdeal R M` with `M` even if `M` is not
finite. Its `kerIdealBaseChange_tmul` and `kerIdealBaseChange_symm_apply` simp
rules specify the pure-tensor and inverse values. Use `open scoped TrivSqZeroExt`
for the canonical opposite action and central scalar structure; the projection
algebra remains local to the construction.

### Left Noetherianity

For `[Ring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]`
and `[SMulCommClass R Rᵐᵒᵖ M]`,
[`TrivSqZeroExt.isNoetherianRing_iff`](../CoherentModules/Algebra/TrivSqZeroExt/Noetherian.lean)
states that `IsNoetherianRing (TrivSqZeroExt R M)` is equivalent to
`IsNoetherianRing R ∧ Module.Finite R M`. These are **left** Noetherianity
and finite generation as a **left** `R`-module, not finite generation as a
bimodule or as a right module. Equivalently,
`TrivSqZeroExt.isNoetherianRing_iff_isNoetherian` uses
`IsNoetherianRing R ∧ IsNoetherian R M` on the right-hand side.

The coefficient ring need not be commutative, and the two module actions need
not be central; they must commute with each other. The carrier universes of
`R` and `M` are independent. No separate `AddCommGroup M` hypothesis is needed.
Import `CoherentModules.Algebra.TrivSqZeroExt.Noetherian` for these criteria.

### Ideal/module transfer

For `[CommRing A]`,
[`Ideal.ideal_property_iff_module_property`](../CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean)
tests a predicate on finite modules over finite-type `A`-algebras via finitely
generated ideals. The predicate must be invariant under compatible algebra and
finite-module isomorphisms and descend along **every** compatible surjective
square-zero algebra map for a finite source module. The base `A : Type uA` may
have a different universe from the common universe of algebra carriers and
their modules. Neither an algebra finite as an `A`-module nor a projective or
coherent module is assumed. The
[client examples](../CoherentModulesTest/Algebra/TrivSqZeroExt/Finite.lean) use
`ZMod 2` for finite nonfree torsion and `ZMod 1` for the zero case, demonstrate
projection base change over `ℕ`, and independently establish the predicate's
isomorphism and descent hypotheses before applying transfer.

## Checks, cost and limits

The default Lake targets include the aggregate and all `CoherentModulesTest`
modules. Stable private test declarations exercise hypotheses, independent
universes and degenerate cases without creating another exported API. The
historical public axiom list is intentionally not a private/generated proof census.
A complete transitive audit also checks private and generated declarations and
their dependencies against the allowed axioms: `propext`, `Classical.choice` and
`Quot.sound`. A successful build checks proofs but does not by itself establish
this closure; a separate stored-body replay is not required for ordinary builds.

### Build and audit resource baseline

A historical cache-ready build of the original 17 library/test modules took
24.865 seconds on a worker with a reported 15 GiB runtime memory limit, using
Lean `v4.34.0-rc2` (compiler `6a10ac8c22beadecabdbb0919c2b50214762f91d`) and
mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`. This is not a benchmark of
the current library, a memory requirement or a portable performance guarantee.
Cold dependency downloads and decompression were not included. Follow the
README's cache-first commands and keep the default library and test targets
enabled; do not replace a failed cache fetch with a mathlib source build.

The historical `LAKE_JOBS=1` setting did not provide effective Lake parallelism
control, and `LEAN_NUM_THREADS=1` is not a global memory cap. Build and audit
memory depends on the workload and machine; neither these settings nor the
historical limit promises a sufficient bound. A complete private/generated
transitive axiom check remains distinct from the 38 selected public checks
and from the historical stored-proof measurement.

This is proof-oriented infrastructure; it promises no efficient executable
algorithm or runtime complexity. Build/check cost depends on the pinned compiler,
dependency cache, machine and selected audit. These existing measurements provide
standalone planning guidance, not a portable performance guarantee. The library
does not yet supply a general coherent-sheaf theory or claim complete coverage
of any mathematical source. See the root README for the library's current scope.
