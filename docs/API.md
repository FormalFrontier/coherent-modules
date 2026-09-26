# Generated API reference

This reference contains all 54 native library display sites, including classes,
constructors and field projections. The nine test/audit modules have no public sites.
Import `CoherentModules` for the library; the test-target modules are separate.
Private/generated proof declarations still require the separate complete audit.
Native display-site counts are not a complete kernel-declaration census.

Headers below are native doc-gen4 display signatures, not complete declarations
with proof bodies. All native visible tokens, including implicit parameters and
literal modifiers such as abbrev, are retained; whitespace alone is normalized.
Native pretty-printing uses each source namespace, notation and type inference;
consult the linked source for suppressed inferred types and universe conventions.
These displayed fragments are not promised to elaborate alone in a fresh namespace.
Source links are relative to this same checkout.

The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).
See [generation instructions](README.md) and the [mathematical guide](Guide.md).
Where no source docstring exists, a separately authored **API note** is labeled explicitly.

## Complete module inventory

| Module | Display sites |
| --- | --- |
| `CoherentModules.Basic` | 28 |
| `CoherentModules.FinitePresentation` | 4 |
| `CoherentModules.Hom` | 1 |
| `CoherentModules.Localization` | 5 |
| `CoherentModules.ModuleCat` | 9 |
| `CoherentModules.TensorProduct` | 1 |
| `CoherentModules.UniversallyCoherent` | 6 |
| `CoherentModules` | 0 |
| `CoherentModulesTest.Axioms` | 0 |
| `CoherentModulesTest.Basic` | 0 |
| `CoherentModulesTest.FinitePresentation` | 0 |
| `CoherentModulesTest.FinitePresentationZero` | 0 |
| `CoherentModulesTest.Hom` | 0 |
| `CoherentModulesTest.Localization` | 0 |
| `CoherentModulesTest.ModuleCat` | 0 |
| `CoherentModulesTest.TensorProduct` | 0 |
| `CoherentModulesTest.UniversallyCoherent` | 0 |

Constructors and class fields may point to the source class span rather
than a separate literal declaration. They are native display sites, not added APIs.

## CoherentModules.Basic

Scope: library.

<a id="api-95ba798c139e1e67"></a>

### Module.IsCoherent

```lean
class Module.IsCoherent (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : Prop
```

A module is coherent if it is finitely generated and every finitely
generated submodule is finitely presented.

[Source](../CoherentModules/Basic.lean#L42-L47) (native source range).

<a id="api-b2c23375a748c274"></a>

### Module.IsCoherent.mk

```lean
constructor Module.IsCoherent.mk : ∀ {R : Type u} [inst : Ring R] {M : Type v} [inst_1 : AddCommGroup M] [inst_2 : Module R M], Module.Finite R M → (∀ (N : Submodule R M), N.FG → Module.FinitePresentation R ↥N) → Module.IsCoherent R M
```

**API note (not a source docstring):** The constructor packages finite generation and finite presentation of every finitely generated submodule. Its native source range is the class declaration, not a separate source-level mk definition.

[Source](../CoherentModules/Basic.lean#L42-L47) (native source range).

<a id="api-17d63eb71ef15997"></a>

### Module.IsCoherent.finite

```lean
theorem Module.IsCoherent.finite {R : Type u} {inst✝ : Ring R} {M : Type v} {inst✝¹ : AddCommGroup M} {inst✝² : Module R M} [self : IsCoherent R M] : Module.Finite R M
```

**API note (not a source docstring):** This class-field projection extracts the finite-generation component of the coherence property.

[Source](../CoherentModules/Basic.lean#L45-L45) (native source range).

<a id="api-7b4e35caa6145935"></a>

### Module.IsCoherent.finitePresentation_submodule

```lean
theorem Module.IsCoherent.finitePresentation_submodule {R : Type u} {inst✝ : Ring R} {M : Type v} {inst✝¹ : AddCommGroup M} {inst✝² : Module R M} [self : IsCoherent R M] (N : Submodule R M) : N.FG → FinitePresentation R ↥N
```

**API note (not a source docstring):** This field of the coherence property supplies finite presentation of a submodule when a proof of finite generation of that submodule is given.

[Source](../CoherentModules/Basic.lean#L46-L46) (native source range).

<a id="api-a65856e877aebe70"></a>

### Module.IsCoherent.toFinite

```lean
instance Module.IsCoherent.toFinite {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherent R M] : Module.Finite R M
```

**API note (not a source docstring):** The typeclass instance extracts finite generation from a coherent module; no coherent-ring hypothesis is required.

[Source](../CoherentModules/Basic.lean#L51-L52) (native source range).

<a id="api-b19d8bcc50f76f41"></a>

### Module.IsCoherent.toFinitePresentation

```lean
instance Module.IsCoherent.toFinitePresentation {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherent R M] : FinitePresentation R M
```

Every coherent module is finitely presented.

[Source](../CoherentModules/Basic.lean#L54-L59) (native source range).

<a id="api-76e8d3ee9b89aca9"></a>

### Module.IsCoherent.iff_finite_and_fg_ker

```lean
theorem Module.IsCoherent.iff_finite_and_fg_ker {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] : IsCoherent R M ↔ Module.Finite R M ∧ ∀ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), f.ker.FG
```

A module is coherent exactly when it is finite and the kernel of every linear map from a
finite-rank free module is finitely generated.

[Source](../CoherentModules/Basic.lean#L61-L85) (native source range).

<a id="api-b4c7a571dfbaa9fc"></a>

### Module.IsCoherent.submodule

```lean
theorem Module.IsCoherent.submodule {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherent R M] (N : Submodule R M) (hN : N.FG) : IsCoherent R ↥N
```

A finitely generated submodule of a coherent module is coherent.

[Source](../CoherentModules/Basic.lean#L87-L99) (native source range).

<a id="api-b0dedccc5b7d55b2"></a>

### Module.IsCoherent.range

```lean
theorem Module.IsCoherent.range {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R M] [IsCoherent R N] (f : M →ₗ[R] N) : IsCoherent R ↥f.range
```

The range of a linear map from a finite module into a coherent module is coherent.

[Source](../CoherentModules/Basic.lean#L101-L105) (native source range).

<a id="api-58005339b521e681"></a>

### Module.IsCoherent.of_exact

```lean
theorem Module.IsCoherent.of_exact {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} {P : Type x} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P] [IsCoherent R M] [IsCoherent R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact ⇑f ⇑g) (hf : Function.Injective ⇑f) (hg : Function.Surjective ⇑g) : IsCoherent R N
```

In a short exact sequence of modules, if the outer modules are coherent, then so is the
middle module.

[Source](../CoherentModules/Basic.lean#L107-L145) (native source range).

<a id="api-b0522e9c97af6a81"></a>

### Module.IsCoherent.ker

```lean
theorem Module.IsCoherent.ker {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [IsCoherent R M] [IsCoherent R N] (f : M →ₗ[R] N) : IsCoherent R ↥f.ker
```

The kernel of a linear map between coherent modules is coherent.

[Source](../CoherentModules/Basic.lean#L147-L156) (native source range).

<a id="api-d6d516a4818fd2c5"></a>

### Module.IsCoherent.finitePresentation_ker

```lean
theorem Module.IsCoherent.finitePresentation_ker {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [IsCoherent R M] [IsCoherent R N] (f : M →ₗ[R] N) : FinitePresentation R ↥f.ker
```

The kernel of a linear map between coherent modules is finitely presented.

[Source](../CoherentModules/Basic.lean#L158-L163) (native source range).

<a id="api-070dd366df634dda"></a>

### Module.IsCoherent.quotient

```lean
theorem Module.IsCoherent.quotient {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherent R M] (N : Submodule R M) (hN : N.FG) : IsCoherent R (M ⧸ N)
```

The quotient of a coherent module by a finitely generated submodule is coherent.

[Source](../CoherentModules/Basic.lean#L165-L194) (native source range).

<a id="api-d776ecff35bf3288"></a>

### Module.IsCoherent.cokernel

```lean
theorem Module.IsCoherent.cokernel {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [IsCoherent R M] [IsCoherent R N] (f : M →ₗ[R] N) : IsCoherent R (N ⧸ f.range)
```

The cokernel of a linear map between coherent modules is coherent.

[Source](../CoherentModules/Basic.lean#L196-L200) (native source range).

<a id="api-e5c56b20fdc72362"></a>

### Module.IsCoherent.of_equiv

```lean
theorem Module.IsCoherent.of_equiv {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [IsCoherent R M] (e : M ≃ₗ[R] N) : IsCoherent R N
```

Coherence is preserved by linear equivalence.

[Source](../CoherentModules/Basic.lean#L202-L213) (native source range).

<a id="api-19915117668836d4"></a>

### Module.IsCoherent.equiv_iff

```lean
theorem Module.IsCoherent.equiv_iff {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) : IsCoherent R M ↔ IsCoherent R N
```

Coherence is invariant under linear equivalence.

[Source](../CoherentModules/Basic.lean#L215-L218) (native source range).

<a id="api-0f2454e21f377da3"></a>

### Module.IsCoherent.of_subsingleton

```lean
instance Module.IsCoherent.of_subsingleton {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [Subsingleton M] : IsCoherent R M
```

A subsingleton module is coherent.

[Source](../CoherentModules/Basic.lean#L220-L224) (native source range).

<a id="api-9a1e602dcad5ec89"></a>

### Module.IsCoherent.of_isNoetherian

```lean
instance Module.IsCoherent.of_isNoetherian {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] : IsCoherent R M
```

A finite module over a Noetherian ring is coherent.

[Source](../CoherentModules/Basic.lean#L226-L232) (native source range).

<a id="api-0c953658c487c55b"></a>

### Module.IsCoherent.prod

```lean
instance Module.IsCoherent.prod {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [IsCoherent R M] [IsCoherent R N] : IsCoherent R (M × N)
```

The product of two coherent modules is coherent.

[Source](../CoherentModules/Basic.lean#L234-L266) (native source range).

<a id="api-3aed8d911296e5aa"></a>

### Module.IsCoherent.pi

```lean
instance Module.IsCoherent.pi {R : Type u} [Ring R] {I : Type u_1} [Finite I] {N : I → Type u_2} [(i : I) → AddCommGroup (N i)] [(i : I) → Module R (N i)] [∀ (i : I), IsCoherent R (N i)] : IsCoherent R ((i : I) → N i)
```

A finite product of coherent modules is coherent.

[Source](../CoherentModules/Basic.lean#L270-L277) (native source range).

<a id="api-9a082264b55f9b09"></a>

### IsCoherentRing

```lean
class IsCoherentRing (R : Type u) [Ring R] : Prop
```

A ring is coherent when it is coherent as a module over itself.

[Source](../CoherentModules/Basic.lean#L287-L289) (native source range).

<a id="api-350fcf7297bc0cde"></a>

### IsCoherentRing.mk

```lean
constructor IsCoherentRing.mk : ∀ {R : Type u} [inst : Ring R], Module.IsCoherent R R → IsCoherentRing R
```

**API note (not a source docstring):** The constructor packages coherence of the ring as a module over itself into the coherent-ring property. Its native source range is the class declaration.

[Source](../CoherentModules/Basic.lean#L287-L289) (native source range).

<a id="api-07bd27189bd8da5a"></a>

### IsCoherentRing.coherent

```lean
theorem IsCoherentRing.coherent {R : Type u} {inst✝ : Ring R} [self : IsCoherentRing R] : Module.IsCoherent R R
```

**API note (not a source docstring):** This class-field projection returns the stored coherence proof for the ring viewed as its own module.

[Source](../CoherentModules/Basic.lean#L289-L289) (native source range).

<a id="api-e37c365cb739caaf"></a>

### IsCoherentRing.toIsCoherent

```lean
instance IsCoherentRing.toIsCoherent (R : Type u) [Ring R] [IsCoherentRing R] : Module.IsCoherent R R
```

**API note (not a source docstring):** The typeclass instance extracts coherence of the ring as a module over itself from the coherent-ring property.

[Source](../CoherentModules/Basic.lean#L291-L292) (native source range).

<a id="api-730482134dc0afc0"></a>

### IsCoherentRing.of_isNoetherian

```lean
instance IsCoherentRing.of_isNoetherian (R : Type u) [Ring R] [IsNoetherianRing R] : IsCoherentRing R
```

Every Noetherian ring is coherent.

[Source](../CoherentModules/Basic.lean#L294-L297) (native source range).

<a id="api-71a8192e82c03bc3"></a>

### isCoherentRing_iff

```lean
theorem isCoherentRing_iff (R : Type u) [Ring R] : IsCoherentRing R ↔ ∀ (I : Ideal R), I.FG → Module.FinitePresentation R ↥I
```

A ring is coherent exactly when its finitely generated ideals are finitely presented.

[Source](../CoherentModules/Basic.lean#L299-L306) (native source range).

<a id="api-6ef8c9f76642f3a3"></a>

### Module.IsCoherent.of_free

```lean
theorem Module.IsCoherent.of_free (R : Type u) [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [Free R M] [Module.Finite R M] [IsCoherentRing R] : IsCoherent R M
```

A finite free module over a coherent ring is coherent.

[Source](../CoherentModules/Basic.lean#L308-L313) (native source range).

<a id="api-c513864e0795e49f"></a>

### Module.finitePresentation_ker_of_free

```lean
theorem Module.finitePresentation_ker_of_free (R : Type u) [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [Free R M] [Module.Finite R M] {N : Type w} [AddCommGroup N] [Module R N] [Free R N] [Module.Finite R N] [IsCoherentRing R] (f : M →ₗ[R] N) : FinitePresentation R ↥f.ker
```

The kernel of a linear map between finite free modules over a coherent ring is
finitely presented.

[Source](../CoherentModules/Basic.lean#L315-L324) (native source range).

## CoherentModules.FinitePresentation

Scope: library.

<a id="api-eab4d6b619afdbb5"></a>

### Module.FinitePresentation.isCoherent

```lean
theorem Module.FinitePresentation.isCoherent {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherentRing R] [FinitePresentation R M] : IsCoherent R M
```

A finitely presented module over a coherent ring is coherent.

[Source](../CoherentModules/FinitePresentation.lean#L44-L51) (native source range).

<a id="api-3fa4deef51992ac1"></a>

### Module.FinitePresentation.ker

```lean
theorem Module.FinitePresentation.ker {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherentRing R] {N : Type w} [AddCommGroup N] [Module R N] [FinitePresentation R M] [FinitePresentation R N] (f : M →ₗ[R] N) : FinitePresentation R ↥f.ker
```

The kernel of a linear map between finitely presented modules over a
coherent ring is finitely presented.

[Source](../CoherentModules/FinitePresentation.lean#L53-L61) (native source range).

<a id="api-17888e29491c94c1"></a>

### Module.FinitePresentation.of_exact_five

```lean
theorem Module.FinitePresentation.of_exact_five {R : Type u} [Ring R] [IsCoherentRing R] {M1 : Type v1} {M2 : Type v2} {M3 : Type v3} {M4 : Type v4} {M5 : Type v5} [AddCommGroup M1] [Module R M1] [AddCommGroup M2] [Module R M2] [AddCommGroup M3] [Module R M3] [AddCommGroup M4] [Module R M4] [AddCommGroup M5] [Module R M5] [Module.Finite R M1] [FinitePresentation R M2] [FinitePresentation R M4] [FinitePresentation R M5] (f12 : M1 →ₗ[R] M2) (f23 : M2 →ₗ[R] M3) (f34 : M3 →ₗ[R] M4) (f45 : M4 →ₗ[R] M5) (h2 : Function.Exact ⇑f12 ⇑f23) (h3 : Function.Exact ⇑f23 ⇑f34) (h4 : Function.Exact ⇑f34 ⇑f45) : FinitePresentation R M3
```

In a sequence of five modules that is exact at the middle three, the middle
module is finitely presented if the first module is finite and the second,
fourth, and fifth modules are finitely presented.

[Source](../CoherentModules/FinitePresentation.lean#L63-L99) (native source range).

<a id="api-dd83f2fc4d1bf333"></a>

### Module.isCoherent_iff_finitePresentation

```lean
theorem Module.isCoherent_iff_finitePresentation {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherentRing R] : IsCoherent R M ↔ FinitePresentation R M
```

Over a coherent ring, a module is coherent exactly when it is finitely
presented.

[Source](../CoherentModules/FinitePresentation.lean#L103-L114) (native source range).

## CoherentModules.Hom

Scope: library.

<a id="api-e5c38e133cba7b9a"></a>

### Module.IsCoherent.linearMap

```lean
theorem Module.IsCoherent.linearMap {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [FinitePresentation R M] [IsCoherent R N] : IsCoherent R (M →ₗ[R] N)
```

Linear maps from a finitely presented module into a coherent module form a coherent module.

[Source](../CoherentModules/Hom.lean#L32-L48) (native source range).

## CoherentModules.Localization

Scope: library.

<a id="api-0478f95be8609646"></a>

### Module.IsCoherent.of_isLocalizedModule

```lean
theorem Module.IsCoherent.of_isLocalizedModule {R : Type u} [CommRing R] (S : Submonoid R) {Rₚ : Type v} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ] {M : Type w} [AddCommGroup M] [Module R M] {Mₚ : Type x} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f] [IsCoherent R M] : IsCoherent Rₚ Mₚ
```

A localization of a coherent module is coherent.

This applies to any ring and module satisfying the respective localization
universal properties. In particular, it does not require the module localization
map to be surjective.

[Source](../CoherentModules/Localization.lean#L40-L81) (native source range).

<a id="api-1ed82eb9435e4dbb"></a>

### Module.IsCoherent.localizedModule

```lean
instance Module.IsCoherent.localizedModule {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R) [IsCoherent R M] : IsCoherent (Localization S) (LocalizedModule S M)
```

The canonical localization of a coherent module is coherent.

[Source](../CoherentModules/Localization.lean#L83-L88) (native source range).

<a id="api-a3742115cdb33768"></a>

### Module.IsCoherent.away

```lean
theorem Module.IsCoherent.away {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [IsCoherent R M] (r : R) : IsCoherent (Localization.Away r) (LocalizedModule.Away r M)
```

A coherent module remains coherent after localization away from an element.

[Source](../CoherentModules/Localization.lean#L90-L95) (native source range).

<a id="api-bdede9583cd5b21c"></a>

### Module.IsCoherent.of_localizationSpan'

```lean
theorem Module.IsCoherent.of_localizationSpan' {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Set R) (hs : Ideal.span s = ⊤) {Mₚ : ↑s → Type w} [(g : ↑s) → AddCommGroup (Mₚ g)] [(g : ↑s) → Module R (Mₚ g)] {Rₚ : ↑s → Type x} [(g : ↑s) → CommRing (Rₚ g)] [(g : ↑s) → Algebra R (Rₚ g)] [∀ (g : ↑s), IsLocalization.Away (↑g) (Rₚ g)] [(g : ↑s) → Module (Rₚ g) (Mₚ g)] [∀ (g : ↑s), IsScalarTower R (Rₚ g) (Mₚ g)] (f : (g : ↑s) → M →ₗ[R] Mₚ g) [∀ (g : ↑s), IsLocalizedModule (Submonoid.powers ↑g) (f g)] (h : ∀ (g : ↑s), IsCoherent (Rₚ g) (Mₚ g)) : IsCoherent R M
```

Coherence descends from arbitrary realizations of localizations away from a
set spanning the unit ideal.

[Source](../CoherentModules/Localization.lean#L97-L124) (native source range).

<a id="api-86ae5835c6c38712"></a>

### Module.IsCoherent.of_localizationSpan

```lean
theorem Module.IsCoherent.of_localizationSpan {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Set R) (hs : Ideal.span s = ⊤) (h : ∀ (g : ↑s), IsCoherent (Localization.Away ↑g) (LocalizedModule.Away (↑g) M)) : IsCoherent R M
```

Coherence descends from canonical localizations away from a set spanning
the unit ideal.

[Source](../CoherentModules/Localization.lean#L126-L135) (native source range).

## CoherentModules.ModuleCat

Scope: library.

<a id="api-86c116ce63be8006"></a>

### ModuleCat.isCoherent

```lean
def ModuleCat.isCoherent (R : Type u) [Ring R] : CategoryTheory.ObjectProperty (ModuleCat R)
```

The property that the underlying module of an object of `ModuleCat R` is coherent.

[Source](../CoherentModules/ModuleCat.lean#L37-L39) (native source range).

<a id="api-8480f3105dd68410"></a>

### ModuleCat.isCoherent_iff

```lean
theorem ModuleCat.isCoherent_iff {R : Type u} [Ring R] (M : ModuleCat R) : isCoherent R M ↔ Module.IsCoherent R ↑M
```

Membership in `ModuleCat.isCoherent` is the unbundled coherent-module predicate.

[Source](../CoherentModules/ModuleCat.lean#L42-L45) (native source range).

<a id="api-c8a069c17d714474"></a>

### ModuleCat.isCoherentIsClosedUnderIsomorphisms

```lean
instance ModuleCat.isCoherentIsClosedUnderIsomorphisms (R : Type u) [Ring R] : (isCoherent R).IsClosedUnderIsomorphisms
```

**API note (not a source docstring):** An isomorphism in ModuleCat transports coherence through its underlying linear equivalence.

[Source](../CoherentModules/ModuleCat.lean#L47-L51) (native source range).

<a id="api-3723a58e3fee7236"></a>

### ModuleCat.isCoherentContainsZero

```lean
instance ModuleCat.isCoherentContainsZero (R : Type u) [Ring R] : (isCoherent R).ContainsZero
```

**API note (not a source docstring):** The coherent-module object property contains a zero object, represented here by the subsingleton module PUnit.

[Source](../CoherentModules/ModuleCat.lean#L53-L58) (native source range).

<a id="api-394849e8485ad26e"></a>

### ModuleCat.isCoherentIsClosedUnderKernels

```lean
instance ModuleCat.isCoherentIsClosedUnderKernels (R : Type u) [Ring R] : (isCoherent R).IsClosedUnderKernels
```

**API note (not a source docstring):** Kernels of morphisms between coherent ModuleCat objects remain coherent, using the underlying linear-map kernel and its categorical comparison.

[Source](../CoherentModules/ModuleCat.lean#L60-L69) (native source range).

<a id="api-52f179db20daee0e"></a>

### ModuleCat.isCoherentIsClosedUnderCokernels

```lean
instance ModuleCat.isCoherentIsClosedUnderCokernels (R : Type u) [Ring R] : (isCoherent R).IsClosedUnderCokernels
```

**API note (not a source docstring):** Cokernels of morphisms between coherent ModuleCat objects remain coherent, by the quotient-by-range construction.

[Source](../CoherentModules/ModuleCat.lean#L71-L82) (native source range).

<a id="api-ad43d6ec4a5813e5"></a>

### ModuleCat.isCoherentIsClosedUnderBinaryProducts

```lean
instance ModuleCat.isCoherentIsClosedUnderBinaryProducts (R : Type u) [Ring R] : (isCoherent R).IsClosedUnderBinaryProducts
```

**API note (not a source docstring):** A binary product of coherent objects of ModuleCat is coherent. This closure is part of the inherited full-subcategory construction.

[Source](../CoherentModules/ModuleCat.lean#L84-L97) (native source range).

<a id="api-516bc204bd29ae94"></a>

### ModuleCat.isCoherentIsClosedUnderFiniteProducts

```lean
instance ModuleCat.isCoherentIsClosedUnderFiniteProducts (R : Type u) [Ring R] : (isCoherent R).IsClosedUnderFiniteProducts
```

**API note (not a source docstring):** The coherent-module object property is closed under finite products, using the binary-product and zero-object instances. The base ring need not be coherent.

[Source](../CoherentModules/ModuleCat.lean#L99-L101) (native source range).

<a id="api-d34fb71470b6f153"></a>

### CoherentModuleCat

```lean
abbrev CoherentModuleCat (R : Type u) [Ring R] : Type (max u (v + 1))
```

The full subcategory of coherent modules over `R`.

Its `Abelian` instance is supplied by
`Mathlib.CategoryTheory.Abelian.Subcategory` from the closure instances above.

[Source](../CoherentModules/ModuleCat.lean#L105-L110) (native source range).

## CoherentModules.TensorProduct

Scope: library.

<a id="api-81e413cffcc3aefc"></a>

### Module.IsCoherent.tensorProduct

```lean
theorem Module.IsCoherent.tensorProduct {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N] [FinitePresentation R M] [IsCoherent R N] : IsCoherent R (TensorProduct R M N)
```

The tensor product of a finitely presented module and a coherent module is coherent.

[Source](../CoherentModules/TensorProduct.lean#L35-L51) (native source range).

## CoherentModules.UniversallyCoherent

Scope: library.

<a id="api-fa47c4816913f51d"></a>

### IsUniversallyCoherent

```lean
class IsUniversallyCoherent (R : Type u) [CommRing R] : Prop
```

A commutative ring is universally coherent (for target algebras in `Type v`) if every
finitely presented commutative algebra in that universe is a coherent ring.

The target-algebra universe is deliberately independent of the universe containing the base
ring. Use `IsUniversallyCoherent.{u, v} R` when that universe is not inferred from an algebra.

[Source](../CoherentModules/UniversallyCoherent.lean#L31-L38) (native source range).

<a id="api-282eedd2884eb910"></a>

### IsUniversallyCoherent.mk

```lean
constructor IsUniversallyCoherent.mk : ∀ {R : Type u} [inst : CommRing R], (∀ (A : Type v) [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.FinitePresentation R A], IsCoherentRing A) → IsUniversallyCoherent R
```

**API note (not a source docstring):** The constructor packages coherence of every finitely presented commutative algebra in the chosen target universe. Its native source range is the class declaration.

[Source](../CoherentModules/UniversallyCoherent.lean#L31-L38) (native source range).

<a id="api-45a977474bfdda74"></a>

### IsUniversallyCoherent.isCoherentRing

```lean
theorem IsUniversallyCoherent.isCoherentRing (R : Type u) {inst✝ : CommRing R} [self : IsUniversallyCoherent R] (A : Type v) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] : IsCoherentRing A
```

**API note (not a source docstring):** This field returns coherence of a finitely presented commutative algebra in the class's specified target universe. The target universe is independent of the base-ring universe.

[Source](../CoherentModules/UniversallyCoherent.lean#L37-L37) (native source range).

<a id="api-d16925e210b76932"></a>

### IsUniversallyCoherent.toIsCoherentRing

```lean
instance IsUniversallyCoherent.toIsCoherentRing (R : Type u) [CommRing R] [IsUniversallyCoherent R] : IsCoherentRing R
```

A universally coherent commutative ring is coherent as a ring.

[Source](../CoherentModules/UniversallyCoherent.lean#L42-L45) (native source range).

<a id="api-bc2de908aa320eac"></a>

### IsUniversallyCoherent.isCoherentRing_of_algEquiv

```lean
theorem IsUniversallyCoherent.isCoherentRing_of_algEquiv (R : Type u) {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.FinitePresentation R A] [IsUniversallyCoherent R] (e : A ≃ₐ[R] B) : IsCoherentRing B
```

Universal coherence gives coherence after replacing a finitely presented algebra by an
equivalent algebra, including when the two carrier types live in different universes.

[Source](../CoherentModules/UniversallyCoherent.lean#L47-L54) (native source range).

<a id="api-e2b8b37b1c95ad6e"></a>

### IsUniversallyCoherent.of_isNoetherian

```lean
instance IsUniversallyCoherent.of_isNoetherian (R : Type u) [CommRing R] [IsNoetherianRing R] : IsUniversallyCoherent R
```

Every Noetherian commutative ring is universally coherent.

[Source](../CoherentModules/UniversallyCoherent.lean#L56-L62) (native source range).
