# API reference generation

[API.md](API.md) documents all 54 native display sites in the seven mathematical
leaves: classes, constructors, class fields, instances, definitions and theorems.
The aggregate and nine test/audit modules are included in the complete
17-module inventory even though they have no public native display sites.
The test modules are not re-exported by `CoherentModules`.

Read the [mathematical guide](Guide.md) for hypotheses and usage and
[CREDITS.md](CREDITS.md) for provenance. Native display sites are not the complete
kernel-declaration inventory: private examples, helpers and generated declarations
also belong to the separate raw/stored-proof audit.

## Preserved information

The bounded adapter preserves all native visible header tokens, including implicit
arguments and literal modifiers, normalizing whitespace only. It verifies each
module/name/kind, signature hash, docstring hash and source range against the fixed
inventory. Native pretty-printing depends on source namespaces, notation and type
inference; displayed fragments are not promised to elaborate in isolation.

There are 39 native source docstrings and 15 separately authored explanations,
labeled **API note (not a source docstring)**. The latter live in
`scripts/api_notes.json` and require semantic review; they are not fabricated
source documentation. Constructors and class-field projections may point to the
whole class declaration. Twelve additional nonprivate raw names, such as generated
recursors, have no native display site; the separate proof inventory accounts for
them rather than inventing documentation signatures.

This release ships Markdown, source links and JSON provenance, not the native HTML
website, JavaScript, styles, fonts, search or dependency documentation. No external
documentation host is required to read its own API. Historical native source URLs
are checked as exact strings, not claimed to be live public web links. All shipped
API source links are relative to this same checkout.

## Native reproduction

Use a separate unchanged doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, including its committed manifest,
with Lean `v4.34.0-rc2`. Build that core-only tool with `lake build doc-gen4`.
Do not add it to this library or change the mathematical dependency pins.
In the library checkout, first successfully fetch the matching mathlib cache and
build all default targets as described in the root README. The following Bash
commands require Python3 and all 17 built modules:

```sh
docgen_executable=/absolute/path/to/doc-gen4
docs_work=$(mktemp -d)
mkdir "$docs_work/analysis" "$docs_work/rendered"
source_revision=$(python3 -c 'import json; print(json.load(open("docs/api-manifest.json"))["analyzed_source_revision"])')
for leaf in Basic FinitePresentation Hom Localization ModuleCat TensorProduct UniversallyCoherent; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "CoherentModules.$leaf" api.db "https://github.com/FormalFrontier/coherent-modules/blob/$source_revision/CoherentModules/$leaf.lean"
done
lake env "$docgen_executable" single --build "$docs_work/analysis" CoherentModules api.db "https://github.com/FormalFrontier/coherent-modules/blob/$source_revision/CoherentModules.lean"
for leaf in Axioms Basic FinitePresentation FinitePresentationZero Hom Localization ModuleCat TensorProduct UniversallyCoherent; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "CoherentModulesTest.$leaf" api.db "https://github.com/FormalFrontier/coherent-modules/blob/$source_revision/CoherentModulesTest/$leaf.lean"
done
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" --source-revision "$source_revision" --check
python3 -B scripts/test_generate_api.py --native-data "$docs_work/rendered/doc-data"
```

Create both directories before invoking the native SQLite opener. Run the tool in
this project's `lake env` so imports resolve to its pinned compiled modules.
Retain actual argv, output, exit status, resolved artifacts and both manifests;
native warnings or failures must not be hidden. `single` receives a URL without
fragment; the native linker adds `#Lstart-Lend`. The adapter requires the exact
repository, full revision, module-specific path and recorded bounded range.

## Independent public history and data checks

`api-manifest.json` binds all 17 source files and three configuration/pin files,
module paths, tool/source revisions, three adapter/inventory/note hashes, canonical
native-record hashes, exact display names and the generated API hash. Documentation-
only successors can reuse native evidence through exact equality of all 20 inputs.
Changed mathematical sources or pins require renewed affected native checks.

When the historical source commit exists, the adapter compares every input against
that Git object. A parentless public release need not contain development history.
Only Git's explicit missing-object result, or a source-only tree without a `.git`
marker, enables fallback to the committed manifest's exact hashes. Broken Git
repositories, command failures and wrong object types refuse fallback. `--check`
compares both complete generated files byte for byte. After a reviewed inventory
update, omit `--check` to generate new files from matching native records.

The data tests require the supplied native-record directory and exercise positive
reproduction, malformed records, source/pin drift and source-only/parentless Git
contexts. They do not rerun doc-gen4 or Lean and do not authenticate the provenance
of arbitrary supplied JSON. Real native receipts require independent inspection.
Neither adapter hashes nor successful rendering certify proofs, rights or release
acceptance. Full review remains separate.
