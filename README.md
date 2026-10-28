# goldbach-lean

A Lean 4 project formalizing progress toward **Goldbach's conjecture** and
building reusable analytic number theory, with **Chen's 1+2 theorem** and
**Li–Liu's 1+1.9 theorem** formalized. The separate
[Wu04/Wu08 development](research/wu2008/README.md) derives **1+1.8938**;
its full source build, statement and axiom checks, and final module kernel
replay have passed.

The Li–Liu result proves:

> Every sufficiently large even natural number has a representation
> `N = p + r*q`, where `p` and `q` are prime, `r = 1` or `r` is prime, and
> `r^10 ≤ q^9`.

It also proves the strict `0.0004` lower bound for the number of distinct prime
first summands satisfying this condition, in the Liu singular-series normalization.
The earlier **1+2** result remains available through its original import and
public names: every sufficiently large even natural number is a prime plus
another prime or a product of two primes, whose factors may be equal.

The [release notes](docs/RELEASE_NOTES.md) describe the new results and retain the
historical v1.0.0 record. The [source-size report](docs/SOURCE_SIZE.md) gives the
current theorem import-closure sizes and measured refactoring changes.
The [structural Chen audit](docs/CHEN_REDUNDANCY_AUDIT.md) records a net saving
of 115,586 effective main-library lines. The subsequent
[comparison with five original papers](docs/CHEN_PAPER_COMPARISON.md)
shares three finite Selberg optimizer proofs and saves another 598 lines.
The current Chen import closure contains 99,214 effective code lines.
The [implemented Li–Liu cleanup](docs/LILIU_CLEANUP.md) follows the
[original-paper audit](docs/LILIU_REDUNDANCY_AUDIT.md), unifies the count and
existence routes, removes duplicate certificates and separates generic sieve
factors from Chen applications. Two waves saved 30,897 main-library lines. The
[continuity follow-up](docs/LILIU_CONTINUITY_CLEANUP.md) saves another 60 lines
using existing one-sided-neighborhood lemmas. The
[shared-foundation follow-up](docs/LILIU_LOG_KERNEL_CLEANUP.md) saves another
11 main lines and 1,086 Li–Liu import-closure lines, counting both
new modules and all moved code. The
[finite-cell calculus follow-up](docs/LILIU_GRID_CALCULUS_CLEANUP.md) shares integration
and convergence arguments across six grids and saves another 89 main lines.
The [shared-lemma follow-up](docs/LILIU_SHARED_LEMMA_CLEANUP.md) removes another
84 production lines and drops redundant evenness assumptions from three internal
Euler positivity statements. The
[local-product follow-up](docs/LILIU_PRODUCT_CLEANUP.md) shares the uniform sieve-product
witness and normalized error payments, saving another 192 lines including its
new shared module. The [carrier and growth follow-up](docs/LILIU_CARRIER_CLEANUP.md)
shares exact carrier and scale-membership proofs and uses Mathlib's finite-fiber
bound, saving another 154 main lines including all moved bodies and imports.
The [endpoint follow-up](docs/LILIU_ENDPOINT_CLEANUP.md) shares exact endpoint
positivity, floor-scale and large-divisor bounds, saving another 78 main lines
including all moved proof bodies. The [low-conductor/Pan follow-up](docs/LILIU_LOW_BUDGET_CLEANUP.md)
shares the generic low-conductor budget and Pan maximum bound, saving another
187 main lines, counting all shared code. The [finite coprimality-gate follow-up](docs/LILIU_GATE_BUDGET_CLEANUP.md)
lets B10 specialize G11's general finite-support estimate, saving another 181 lines,
including all 116 lines in the new common provider. The
[finite-helper follow-up](docs/LILIU_FINITE_HELPER_CLEANUP.md) reuses existing finite-sum,
log-payment and inclusive grid bounds, saving another 34 main lines with all moved
code counted. The [boundary-integral follow-up](docs/LILIU_BOUNDARY_INTEGRAL_CLEANUP.md)
shares the exact B9/G9 excess-cover estimates and low-integral positivity, saving
another 127 lines with all moved code counted. The
[quartic-log follow-up](docs/LILIU_QUARTIC_LOG_CLEANUP.md) shares B10/S2's identical
quartic remainder payment, saving another 16 main/Li–Liu lines including its full
shared proof. Chen's source closure grows by 16 lines through that shared provider.
The [shared-calculus follow-up](docs/LILIU_SHARED_CALCULUS_CLEANUP.md) reuses the
original G11 derivative/Fubini proofs and global author-weight cap, and simplifies
two complex-power identities, saving another 27 main/Li–Liu lines and 6 Chen lines.
The [finite-prefix follow-up](docs/LILIU_FINITE_PREFIX_CLEANUP.md) shares the original
squarefree-divisor and sorted-prefix proofs, saving another 66 main/Li–Liu lines
and 49 Chen lines.
Current main size: 201,756 effective lines; current Li–Liu import closure:
194,201 lines.
The [recorded build benchmarks](docs/BUILD_BENCHMARK.md)
measure the v1.0.0-rc1 and v1.0.0 **1+2** developments.

**[Project homepage](https://subfish-zhou.github.io/goldbach-lean/)**
· **[Lean API documentation](https://subfish-zhou.github.io/goldbach-lean/docs/)**
· **[Interactive proof Blueprint](https://subfish-zhou.github.io/goldbach-lean/blueprint/)**

The Lean API documentation covers all four project libraries, with declaration
search, source links, and import navigation. The complete local publication
layout includes the Li–Liu mathematical proof structure and paper correspondence
at `/report/`. Optional dependency panels in the Blueprint and API expose the
compiled dependency data from internal static assets. See [how the website is built and published](docs/DOCUMENTATION.md).

| Read the mathematics | Explore the proof | Check the result |
|---|---|---|
| [Theorems and normalization](docs/THEOREMS.md) | [Architecture and source map](docs/ARCHITECTURE.md) | [Verification and trust boundary](docs/VERIFICATION.md) |

## Proof at a glance

The following roadmap describes the Chen 1+2 route. The Li–Liu extension has
its own [public entry and source route](docs/ARCHITECTURE.md#liliu-extension).

```mermaid
flowchart BT
  distribution["Prime distribution and analytic estimates"] --> lower["Weighted lower sieve"]
  comparison["Jurkat-Richert functions and Suzuki comparison"] --> lower
  distribution --> upper["Switched-source Selberg upper sieve"]
  lower --> counting["Finite counting: lower bound minus triple penalty"]
  upper --> counting
  counting --> quantitative["Quantitative representation bound"]
  quantitative --> chen["Chen's theorem: prime + at most two primes"]
```

This is a mathematical roadmap: arrows point from an input to the result it
supports, and may summarize several modules. The [source map](docs/ARCHITECTURE.md)
separates this view from direct imports and compiled declaration dependencies.

The [interactive Blueprint](https://subfish-zhou.github.io/goldbach-lean/blueprint/)
renders selected declaration dependencies from LeanArchitect, with links to their
Lean source. This curated mathematical view is distinct from the module import
graph and the compiled declaration graph available through these panels. Imports
record module access; only the separate compiled `value` references record
actual static uses within stored proofs or definitions. The declaration graph
also keeps `type` and `recursorRHS` references separate.

The release procedure for this documentation update builds and validates the
complete static site locally, then publishes it independently to `gh-pages`
from a fresh staging checkout. Lean CI retains the full warning-free build, source/statement/axiom
checks, script tests, and replay of `Goldbach.Theorem`, `Goldbach.Checks`,
`Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`;
it does not generate or deploy the website. A reused API artifact may document
an earlier source version than the website: record both exact revisions and
preserve the API's original source links. Follow the
[deployment procedure](docs/DOCUMENTATION.md#regression-tests-and-deployment)
and read back the live build records after Pages deploys to determine which
version is online.

## Main results

The two developments have separate imports over shared analytic foundations.
Use `import Goldbach` for the established 1+2 interface,
`import Goldbach.OnePlusOneNine` for 1+1.9, or `import Goldbach.All` for both.

```lean
import Goldbach.OnePlusOneNine

#check Goldbach.one_plus_one_nine
#check Goldbach.one_plus_one_nine_real
#check Goldbach.one_plus_one_nine_count
#check Goldbach.one_plus_one_nine_lower_bound
```

The natural-power theorem retains the exact `r^10 ≤ q^9` condition; the real-power
version states `r ≤ q^((19/10 : ℝ) - 1)`. The count theorem gives
`(1/2500) * liuSingularSeries N * N / (Real.log N)^2 < D19 N`, where `D19`
counts different eligible primes `p`. The stronger lower-bound family allows
each fixed real `κ < 515093/800000000`, with a threshold depending on `κ`.
See [the precise statements and normalization](docs/THEOREMS.md).

The original Chen interface is unchanged:

```lean
import Goldbach

#check Goldbach.chen_theorem
#check Goldbach.representation_lower_bound
```

`Goldbach.chen_theorem` proves `Goldbach.ChenTheorem`. The specification in
[`Goldbach/Statement.lean`](Goldbach/Statement.lean) is deliberately independent
of the sieve implementation:

```lean
∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
  ∃ p q : ℕ, p.Prime ∧
    (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q
```

The quantitative theorem gives an eventual lower bound of
`0.67 * liuSingularSeries N * N / (Real.log N)^2` for the cardinality of the
actual good-representation set, for even `N`. See
[`docs/THEOREMS.md`](docs/THEOREMS.md) for definitions and normalization.

## Wu04/Wu08: 1+1.8938

The self-contained [research development](research/wu2008/README.md) has its own
source manifest, build driver, and acceptance checks. Its final module is
[`WR2ClassicalCertificate`](research/wu2008/src/WR2ClassicalCertificate.lean),
whose theorem `WuPaper.ClassicalSlots.one8938` states that every sufficiently
large even `N` has `N = p + r*q`, with `p` and `q` prime, `r = 1` or prime,
and `r^5000 ≤ q^4469`. The previous `one894` interface is retained.

The complete 4,151-module research scope, independent literal statement and axiom
checks, and final module kernel replay have passed. The production receipt check
reuses 3,500 actual compiled source proofs and verifies 651 unchanged dependencies.
Follow the research README for separate verification commands and acceptance records.
The latest [structural compression](docs/WU_STRUCTURAL_COMPRESSION.md) saves 7,612
effective lines while preserving precision and budgets. The final theorem import
closure now contains 525,529 effective lines, 601,107 fewer than the original version.
The preceding [LiuPan lemma pruning](docs/WU_LIUPAN_PRUNING.md) remains a historical
accepted phase with 383 removed declarations and 10,924 lines saved.

The [paused next Hf4 candidate](research/wu-hf4-constructive-wip/README.md) is
preserved separately with its producer and partial verification evidence; it is
excluded from the accepted totals above.

## Build and check

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
unset LEAN_PATH LEAN_SRC_PATH
lake exe cache get
lake --wfail build
python3 scripts/check.py
lake env lean Goldbach/Checks.lean
lake env leanchecker --verbose Goldbach.Theorem
```

The toolchain and all Git dependencies are pinned by `lean-toolchain` and
`lake-manifest.json`. The checkout contains the complete local source closure.
`lake exe cache get` downloads Mathlib's compiled cache; the project proofs are
built from source. `scripts/check.py` runs separate statement and axiom probes
for Chen 1+2 and Li–Liu 1+1.9. `Goldbach/Checks.lean` retains the Chen checks;
`Goldbach/OnePlusOneNineChecks.lean` checks the new interface. The `leanchecker`
command above replays the Chen public module against cached imports. The
[verification guide](docs/VERIFICATION.md) gives the Li–Liu inspection and replay
commands as well.

The checks reject proof placeholders and custom axioms in the shipped source,
verify the public theorem axiom reports against Lean's standard classical
axioms (`propext`, `Classical.choice`, `Quot.sound`), and check source hygiene.
Read [`docs/VERIFICATION.md`](docs/VERIFICATION.md) for the exact coverage and
limitations.

### Focused builds and upgrading an existing checkout

```sh
lake build Goldbach.Theorem          # Chen 1+2
lake build Goldbach.OnePlusOneNine   # Li–Liu 1+1.9
lake build Goldbach.All              # both public interfaces
lake build                          # full project
```

If you have already built the project, keep `.lake/` and update your checkout
without cleaning it. To update an existing `main` checkout:

```sh
git switch main
git pull --ff-only
lake build Goldbach.OnePlusOneNine
```

To use the integration branch instead, run `git fetch origin`, then
`git switch integrate/liliu19-latest`. If that branch is not yet local, use
`git switch --track origin/integrate/liliu19-latest` instead. Preserve or commit
any local work before switching branches.

The package configuration, toolchain and dependency pins are unchanged. Lake
can reuse unchanged dependency artifacts and rebuilds new or changed modules
and affected consumers as needed. Keep the existing `.lake/` directory; rebuild
work depends on your cache state and selected target.

## Organization

- `Goldbach/`: independent statement, public theorems, and acceptance checks.
- `MathlibNt/`: Chen and Li–Liu sieve and analytic proof implementations.
- `AnalyticNumberTheory/`: reusable prime-distribution, Mertens, and sieve results.
- `PrimeNumberTheoremAnd/`: the attributed, adapted prime-number-theorem source closure.
- `scripts/`: reproducible source and trust checks.
- `docs/`: theorem map, architecture, provenance, and verification instructions.
- `research/wu2008/`: the separately built and accepted Wu04/Wu08 1+1.8938 proof.

The proof uses a modern combination of Jurkat–Richert/Richert linear sieve,
Suzuki comparison results, Selberg upper sieve, and proved distribution bounds.
The [architecture guide](docs/ARCHITECTURE.md) explains how these ingredients
combine to prove the public results.

## Sources and license

Distributed under Apache-2.0. Upstream copyright notices are retained.
This project builds on `UyNewNas/chen-theorem-lean`,
`UyNewNas/analytic-number-theory-lean`, Mathlib, and the adapted source closure
of `AlexKontorovich/PrimeNumberTheoremAnd`. Attribution is described in
[`docs/PROVENANCE.md`](docs/PROVENANCE.md).
