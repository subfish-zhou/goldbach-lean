# API documentation and proof Blueprint

The documentation site has two complementary views:

- **Lean API documentation** at the site root: doc-gen4 module pages,
  declaration search, declaration anchors, source links, imports, and
  reverse-import links for the documented modules.
- **Proof Blueprint** at `blueprint/`: the existing mathematical narrative and
  dependency graph. The Blueprint is not a substitute for API documentation.

The public mathematical endpoint is the unconditional **1 + 2 theorem**:
Chen's theorem, not the binary Goldbach conjecture. Lean's standard foundational
axioms (`propext`, `Classical.choice`, and `Quot.sound`) are part of the logical
foundation, not additional mathematical assumptions. Generating documentation
is not a proof or axiom audit; see [VERIFICATION.md](VERIFICATION.md).

## Pinned generator and isolation

The nested `docbuild/` Lake project uses Lean `v4.33.0-rc1` and doc-gen4's
[official matching tag](https://github.com/leanprover/doc-gen4/tree/v4.33.0-rc1),
frozen at `498457dedc5bf2eb884c5100804ef24c96b92a08`. Its committed manifest pins
all generator dependencies. It does **not** require the theorem project as a
Lake dependency and does not change the core `lakefile.toml`, `lake-manifest.json`,
or `lean-toolchain`. Documentation dependencies live under
`docbuild/.lake/packages`; the existing mathlib installation is read in place,
not copied into a second Lake dependency tree.

The [upstream README](https://github.com/leanprover/doc-gen4/blob/v4.33.0-rc1/README.md)
recommends a nested Lake project. Its normal `:docs` facets recursively document
imports and Lean core. At this pinned version there is no external-documentation
base-URL option in those facets or the renderer. To avoid generating all mathlib
HTML, `GoldbachDocs.lean` calls the upstream analyzer, HTML renderer, and search
index writer for **project modules only**. It retains the complete imported
name-to-module context, so declaration links can still be resolved. A small
Python postprocessor redirects dependency links in HTML and search/header JSON.
No doc-gen4 source patch is applied.

Dependency API links use <https://leanprover-community.github.io/mathlib4_docs/>.
That site is a **moving documentation reference**, not a version-pinned build
input; a declaration or anchor can differ from this project's pinned mathlib.
Use `--mathlib-docs URL` to select a compatible hosted snapshot when available.
LeanArchitect imports link to their pinned GitHub source because this build does
not assume an independently hosted LeanArchitect API site. Source links for
project declarations are pinned to the checkout's Git commit and line ranges.
A local, unpushed commit's source links become publicly resolvable only after that
commit is published. Generate from a clean, committed release checkout.

## Build a complete API site

Requirements: the pinned Lean/Lake toolchain, a C compiler, Git, Python 3.10 or
newer, network access for the generator's first build, and sufficient disk space
for its native executable and the project API pages. First finish the normal
project build. The documentation command deliberately **does not compile project
proofs**, and should not race an active project build:

```sh
lake --wfail build
python3 scripts/build_docs.py
```

The default output is `docbuild/.lake/build/site/`. It must not already exist:
choose a fresh path with `--output` for later runs. Each invocation generates into
a fresh intermediate directory, so stale modules cannot leak into a new site.
A failed run leaves diagnostic intermediates under
`docbuild/.lake/build/api-run-*`, but does not publish a successful output directory.
These are ignored build products, not files to commit.

Without `--module`, the script enumerates **all source modules**, not just facade
import closures, in all four libraries:

- `Goldbach`
- `MathlibNt`
- `AnalyticNumberTheory`
- `PrimeNumberTheoremAnd`

It builds only the generator, reads compiled `.olean` artifacts and their runtime
sidecars, renders modules with at most two concurrent processes by default,
waits for every module, and writes the upstream declaration and header search
indexes. Use `--jobs 1` to serialize rendering, or a larger value when memory
and CPU resources permit. It then checks module coverage, declaration search anchors,
and local HTML asset/link targets. It fails if doc-gen4 reports that declaration
analysis was omitted. It does not produce mathlib, Lean core, or generator-library
HTML. The global upstream tactic catalogue is not populated; tactic declarations
remain documented on their project module pages.

`build-info.json` records the source revision, toolchain, generator and mathlib
revisions, renderer concurrency, module inventory, declaration count, external
link count, and whether
this is a full or partial build. A partial build must not be presented as full
release documentation.

## Small-module smoke test

```sh
lake --wfail build Goldbach.Statement
python3 scripts/build_docs.py --module Goldbach.Statement \
  --output docbuild/.lake/build/smoke-site
python3 -m http.server 8000 --directory docbuild/.lake/build/smoke-site
```

Visit <http://localhost:8000/Goldbach/Statement.html>, search for
`Goldbach.ChenTheorem`, follow its declaration anchor and source link, and inspect
the external `Nat.Prime` and import links. Serve over HTTP: opening `file://` pages
breaks the fetch-based search interface. The source-only regression tests are:

```sh
python3 -m unittest discover -s scripts -p test_build_docs.py -v
```

To read prebuilt artifacts from a separate matching checkout without writing or
running Lake there, add `--artifacts-from /path/to/compiled-checkout`. The script
checks the toolchain, core dependency manifest, selected source hashes, and the
presence of selected `.olean` files. These checks do not establish that all
transitive artifacts are current: the caller must first finish and verify the
corresponding project build. Do not use artifacts from another proof branch.

## Preserve and include the Blueprint

Build the existing Blueprint by the repository's normal Blueprint procedure,
then pass its generated HTML directory:

```sh
python3 scripts/build_docs.py --blueprint blueprint/web \
  --output docbuild/.lake/build/release-site
python3 -m http.server 8000 --directory docbuild/.lake/build/release-site
```

This copies the existing Blueprint output, without modifying its sources, into
`release-site/blueprint/` and adds a Blueprint link to the API home page. Existing
Blueprint declaration links continue to point to their GitHub source locations.
If `--blueprint` is omitted, the output contains only the API site. The API
validator checks local HTML link and asset targets in both trees, including
ordinary fragment anchors. It does not certify graph interaction or external
link availability. Verify those separately before release.

For Pages, upload the **entire generated site directory**, preserving
`declarations/*.bmp` (these are JSON indexes despite their extension), `find/`,
JavaScript/CSS, `.nojekyll`, and optional `blueprint/`. The generator uses relative
site links and works below a project Pages prefix. Publishing, workflow changes,
and release tagging are separate steps: a local build alone does not deploy a
website. Rebuild after the final release commit so source-link revisions match
what is actually published.
