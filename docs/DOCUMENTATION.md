# Project homepage, Lean documentation and proof Blueprint

The website presents the Goldbach research program through three routes:

- **Project homepage** at `/`: research goals, progress, reading routes,
  verification instructions and provenance links. Chen's **1 + 2 theorem** is
  formalized alongside **Li–Liu's 1+1.9 theorem**, with stronger results as
  further research directions. The homepage HTML and CSS live in `website/`.
- **Lean API documentation** at `/docs/`: doc-gen4 module pages, declaration
  search, declaration anchors, source links, imports and reverse-import links
  for the documented modules.
- **Proof Blueprint** at `/blueprint/`: the selected **Chen 1+2** and
  **Li–Liu 1+1.9** routes together with their reusable analytic foundations,
  with links into the implementation.

The completed public theorems give Chen's prime-plus-almost-prime representation
and Li–Liu's constrained `N = p + r*q` representation with `r^10 ≤ q^9`, together
with quantitative bounds for their respective distinct-prime counts.
[THEOREMS.md](THEOREMS.md) defines their precise mathematical scope.
The proofs use Lean's standard logical foundation: `propext`, `Classical.choice`
and `Quot.sound`. [VERIFICATION.md](VERIFICATION.md) describes the source build,
literal statement checks, axiom reports and kernel replay. The documentation
pipeline below renders compiled declarations and checks the resulting site.

The current source entries are `Goldbach` for 1+2, `Goldbach.OnePlusOneNine`
for 1+1.9, and `Goldbach.All` for both. Blueprint annotations in
`Goldbach/Blueprint.lean` select sixteen declarations spanning both proof routes
and the common foundations. Titles and mathematical summaries are authored
there; chapters are written in `blueprint/src/content.tex`. LeanArchitect infers
the selected dependency edges from compiled declarations, and LeanBlueprint
renders the document. `scripts/verify_blueprint.py` checks the node and edge
inventory against `blueprint/graph.json`.

The generated API inventory retains its own `source_revision` in
`docs/build-info.json`. The assembled site's record also distinguishes
`api_source_revision`, `website_source_revision` and `blueprint_source_revision`.
For a homepage/Blueprint preview that reuses an older complete API artifact,
pass `--source-revision COMMIT` to `scripts/build_site.py`; the Blueprint record
must match that website revision. API pages retain their original source links.
The standard CI build generates all three views from the same revision.

## Pinned generator and isolation

The nested `docbuild/` Lake project uses Lean `v4.33.0-rc1` and doc-gen4's
[official matching tag](https://github.com/leanprover/doc-gen4/tree/v4.33.0-rc1),
frozen at `498457dedc5bf2eb884c5100804ef24c96b92a08`. Its committed manifest pins
all generator dependencies. The theorem project and its core `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` remain independent of this generator
project. Documentation dependencies live under `docbuild/.lake/packages`;
the generator reads the theorem project's existing mathlib installation in place.

The [upstream README](https://github.com/leanprover/doc-gen4/blob/v4.33.0-rc1/README.md)
recommends a nested Lake project. Its normal `:docs` facets recursively document
imports and Lean core. At this pinned version those facets and the renderer
provide no external-documentation base-URL option. `GoldbachDocs.lean` therefore
calls the unmodified upstream analyzer, HTML renderer and search-index writer
for **project modules only**. It retains the complete imported name-to-module
context for declaration links. A Python postprocessor redirects dependency links
in HTML and search/header JSON.

Dependency API links use <https://leanprover-community.github.io/mathlib4_docs/>.
This moving documentation reference can contain declarations or anchors that
differ from the project's pinned mathlib. Use `--mathlib-docs URL` to select a
compatible hosted snapshot when available. LeanArchitect imports link to their
pinned GitHub source. Source links for project declarations use the checkout's
Git commit and line ranges. Generate from a clean, committed release checkout,
and publish that commit to make its source links publicly resolvable.

## Build a complete API site

Requirements: the pinned Lean/Lake toolchain, a C compiler, Git, Python 3.10 or
newer, network access for the generator's first build, and sufficient disk space
for its native executable and the project API pages. Finish the project build
before starting documentation generation, so all compiled proofs and runtime
sidecars are ready and remain stable throughout rendering:

```sh
lake --wfail build
python3 scripts/build_docs.py
```

The default API output is `docbuild/.lake/build/api/`. Choose a fresh path with
`--output` for each later run. Each invocation generates into a fresh intermediate
directory and publishes the output after validation. Failed runs leave diagnostic
intermediates under `docbuild/.lake/build/api-run-*`. These directories are
ignored build products.

With its default module selection, the script enumerates **every source module**
in all four libraries, including modules outside facade import closures:

- `Goldbach`
- `MathlibNt`
- `AnalyticNumberTheory`
- `PrimeNumberTheoremAnd`

It builds the generator, reads the project's compiled `.olean` artifacts and
runtime sidecars, renders the selected modules, waits for every renderer, then
writes the upstream declaration and header search indexes. The main options are:

| Option | Effect |
|---|---|
| `--module NAME` | Select a module; repeat the option to select several. The default selects all four libraries. |
| `--jobs N` | Run at most `N` module renderers concurrently; the default is `2`, and `1` serializes rendering. |
| `--output PATH` | Publish to a new directory after validation. |
| `--artifacts-from PATH` | Read project artifacts and dependencies from a matching compiled checkout. |
| `--mathlib-docs URL` | Set the external dependency API base URL. |
| `--blueprint PATH` | Include an already rendered Blueprint inside a legacy API bundle. |

Choose renderer concurrency to fit available memory and CPU resources. The driver
also defaults `LEAN_NUM_THREADS` to `2` when the environment leaves it unset.
Generated module HTML covers the selected project modules; mathlib, Lean core
and generator-library references link outward. Project tactic declarations appear
on their module pages; the global upstream tactic catalogue remains empty.

Validation checks module coverage, declaration search anchors and local HTML
asset/link targets. Omitted declaration analysis reported by doc-gen4 fails the
run. `build-info.json` records the source revision, toolchain, generator and
mathlib revisions, renderer concurrency, module inventory, declaration count,
external URL count and full/partial scope. Release website assembly requires a
full API build.

## Small-module smoke test and artifact reuse

```sh
lake --wfail build Goldbach.Statement
python3 scripts/build_docs.py --module Goldbach.Statement \
  --output docbuild/.lake/build/smoke-site
python3 -m http.server 8000 --directory docbuild/.lake/build/smoke-site
```

Visit <http://localhost:8000/Goldbach/Statement.html>, search for
`Goldbach.ChenTheorem`, follow its declaration anchor and source link, and inspect
the external `Nat.Prime` and import links. Serve over HTTP so the fetch-based
search interface can load its indexes.

To reuse prebuilt artifacts, add `--artifacts-from /path/to/compiled-checkout`.
First finish and verify the corresponding project build on the same proof
branch, including transitive dependencies. The script reads that checkout in
place and runs Lake only in the documentation generator project. Its preflight
compares the toolchain, core dependency manifest and selected source hashes,
and checks that the selected `.olean` files exist. The completed project build
supplies the freshness guarantee for transitive artifacts.

## Assemble the project website

Build the Blueprint using the [normal procedure](ARCHITECTURE.md#interactive-blueprint),
then assemble it with a full API build:

```sh
python3 scripts/build_docs.py --output docbuild/.lake/build/api
python3 scripts/build_site.py --api docbuild/.lake/build/api \
  --blueprint blueprint/web --output docbuild/.lake/build/site
python3 -m http.server 8000 --directory docbuild/.lake/build/site
```

If the full API output already exists and has been verified, start with the
`build_site.py` command. Use a fresh site output path for each assembly.
The resulting routes are `/`, `/docs/` and `/blueprint/`, relative to the
project's deployment prefix. The API sidebar and Blueprint page headers link
back to the homepage. Blueprint declaration links retain their pinned GitHub
source locations.

`build_site.py` copies the full API output, rendered Blueprint and homepage
assets into a fresh intermediate directory. It adds cross-navigation, checks the
declaration census and local links/anchors, then moves the validated result to
the requested output directory. The input trees remain unchanged. Assembly
works entirely with the existing HTML and assets, so homepage-only changes can
reuse a previously verified full API build and Blueprint.

Both API-only output and the older `build_docs.py --blueprint` bundle are valid
assembly inputs. For a legacy bundle, the copy step omits its nested Blueprint
and places the separately supplied Blueprint at the sibling `/blueprint/`
route. A partial API build fails the assembly preflight.

The homepage's source revision comes from the API build record and identifies
the Lean source used for that API build. The assembled record retains this
revision and separately records the homepage hash and route layout, allowing
homepage changes to reuse the same proof documentation.

The Blueprint's plasTeX configuration selects the `HTML5` renderer, loads
`plastexdepgraph` and `leanblueprint`, copies theme extras, and loads local
packages and templates. It sets `split-level=0`, `localtoc-level=0` and
`mathjax-dollars=False`. LeanArchitect's declaration-only setup macros have
explicit empty HTML templates, so they emit no visible body content while
parser warnings remain enabled.

Link repair maps two historical relative module URLs to their actual
`AnalyticNumberTheory` pages. Links to compiler-generated proof auxiliaries,
auxiliary definitions and constructor indices omitted by doc-gen4 point to the
owning declaration when that owner's anchor exists on the same page. Validation
rejects other missing anchors. Directory routes must contain `index.html`, and
local links must remain within the deployment boundary. The explicitly
registered declaration-search `find/` route handles its fragments in JavaScript;
other HTML fragments are checked against page anchors, with `#top` accepted as
the page-top destination.

`external_url_count` counts distinct external URLs in HTML attributes and API
index/header metadata. Before release, check external link availability and
Blueprint graph interaction in a browser, alongside the local structural checks.

## Regression tests and deployment

Run the source-only regression suites with:

```sh
python3 -m unittest discover -s scripts -p test_build_docs.py -v
python3 -m unittest discover -s scripts -p test_build_site.py -v
```

The site suite exercises API-only and legacy-bundle inputs, preservation of input
trees, cross-navigation and repeated navigation insertion, homepage hashes,
partial-build rejection, revision validation, missing targets, declaration-census
mismatches, directory routes and deployment-boundary escapes. It also checks that
Blueprint navigation is added to the page header while theorem headers remain
intact.

For Pages, upload the **entire generated site directory**, preserving
`docs/declarations/*.bmp` (JSON indexes despite their extension), `docs/find/`,
JavaScript/CSS, root homepage assets, `.nojekyll` and `blueprint/`. Relative site
links support deployment below a project Pages prefix. Publish the site through
the deployment workflow after local validation. Generate the release API from
the final published source commit so declaration source links resolve to that
revision.
