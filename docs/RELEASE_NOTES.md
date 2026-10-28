# Release notes

## Li–Liu shared finite-prefix and divisor proofs (2026-10-27)

Canonical squarefree-divisor sums now reuse Mathlib's existing proof. WF keeps its
public name as a canonical call. The shorter sorted-prefix proof moves into the
canonical provider; both WF prefix/cardinality names reuse it. One existing private
cardinality proof becomes public. All original public statements and rounded
admissibility definitions remain. Four existing files save 66 main/Li–Liu lines
and 49 Chen closure lines, with no new modules or imports. Full build, checks,
five named kernel replays, complete census, tests and local Blueprint pass.
See the [report](LILIU_FINITE_PREFIX_CLEANUP.md).


## Li–Liu shared calculus and author-weight proofs (2026-10-27)

G12 now uses the original G11 log-ratio derivative and four-variable Fubini
proofs through its existing imports. Both original complex-power shift statements
invoke Mathlib's addition law directly. The original global author-weight cap
moves into its definition provider and is shared by both original public names.
All old public names/types, positivity and integrability hypotheses remain.
Counting all promoted/moved code, nine existing files save 27 main/Li–Liu
effective lines and 6 Chen closure lines. No modules or imports are added.
Full build, checks, five named kernel replays, complete census, tests and local
Blueprint pass. See the [report](LILIU_SHARED_CALCULUS_CLEANUP.md).


## Li–Liu shared quartic-log remainder payment (2026-10-27)

B10 and S2 call one shared quartic-log payment theorem in the existing canonical
Liu log-absorption module. Both removed private statements match its complete
kind/type hash. Positive coefficients/errors, real exponents and natural threshold
at least four remain unchanged. Counting all shared code, the main tree and
Li–Liu closure each save 16 effective lines; Chen's source closure grows by 16
through the shared provider. Neither Chen public proof reaches the new helper.
Full build, checks, five named kernel replays, complete census, tests and local
Blueprint pass. All 10,405 old public names/kinds/types remain; one helper is added.
See the [report](LILIU_QUARTIC_LOG_CLEANUP.md).


## Li–Liu shared boundary-integral and low-positivity proofs (2026-10-27)

B9 high and weighted G9 integral error estimates now specialize the existing
finite excess-cover theorem, preserving all original strips, exact areas,
pointwise caps and final error constants. The original unconditional G9
low-integral positivity proof moves into its definition provider and is shared
by both original public names. Five existing files save 127 main/Li–Liu effective
lines, including both direct imports and all moved code. Chen's complete closure
totals are unchanged. Full build, literal/axiom checks, five named kernel replays,
complete type census, script tests and local Blueprint pass. All 10,405 old
public names/kinds/types remain. See the [report](LILIU_BOUNDARY_INTEGRAL_CLEANUP.md).


## Li–Liu finite-sum, log-payment and grid helpers (2026-10-27)

Existing Mathlib sum identities replace two manual ZMod reindexings. Three
log-remainder estimates reuse the genuine Liu singular-series payment, and the
WF transport budget calls the existing general log-power theorem. The inclusive
grid-endpoint proof moves into its existing definition provider and is shared by
the main/secondary consumers. All original public names and types remain. Nine
existing files save 34 main/Li–Liu effective lines and 7 Chen closure lines,
including all moved code and imports. Full source build, literal/axiom checks,
five named kernel replays, complete type census, tests and local Blueprint pass.
See the [report](LILIU_FINITE_HELPER_CLEANUP.md).


## Li–Liu shared finite coprimality-gate budgets (2026-10-27)

B10 now specializes the existing general G11 weighted-support estimate at two
prime factors, retaining the original carrier, signed weights and exact `4*T/b`
constant. Four unchanged public proofs move to one common main-library provider.
Counting all 116 shared lines, the main tree and Li–Liu closure each save 181
effective lines. Chen's complete closure totals are unchanged. Full source build,
literal/axiom checks, five named kernel replays, complete type census, tests and
local Blueprint pass. All 10,405 original public names/kinds/types remain.
See the [report](LILIU_GATE_BUDGET_CLEANUP.md).


## Wu LiuPan lemma pruning (2026-10-27)

Removed 383 unused theorem/lemma declarations without attributes from nine Wu
LiuPan files, preserving every surviving source fragment, definition, instance
and attribute. This saves 10,924 effective lines, 11,516 physical lines and
514,688 bytes. The final theorem closure is 533,141 effective lines; the full
research inventory remains 4,142 modules. All numerical bounds and the exact
`r^5000 ≤ q^4469` endpoint remain unchanged. Full isolated scope, literal/axiom
checks, ten kernel replays and post-adoption production verification pass.
See [the report](WU_LIUPAN_PRUNING.md) and
[acceptance audit](../research/wu-liupan-pruning-audit/validation.json).

## Wu Fifth integer payments (2026-10-27)

Exact integer formulas replace three 1,024-entry Fifth payment tables and their
repeated pointwise certificates. Pairing the signed polynomial coefficients
preserves the degree-12 polynomial exactly and justifies every Nat subtraction.
All original precision, constants, 3,072 payments and 48 block sums remain.
The accepted 4,142-module phase removes 3,779 effective lines and 39 modules.
[Report](WU_FIFTH_INTEGER_PAYMENTS.md).


## Li–Liu shared low-conductor budgets and Pan maxima (2026-10-27)

The identical low-conductor budget moves upstream under its existing public name;
both full higher estimates keep their original ranges and moving endpoints.
LowPrefix reuses existing Pan quotient bounds. One shared Pan maximum theorem
replaces B10/S2 copies, and a generic Mathlib theorem replaces a local squarefree
product induction. Counting shared code and the direct import, the main tree and
Li–Liu closure each save 187 effective lines. Chen's closure grows by +14 lines
through shared providers. No module or auxiliary Lean probe is added. Complete
build, checks, five kernel replays, type census, tests and local Blueprint pass.
Original public kinds/types, constants and numerical precision are retained.
See the [report](LILIU_LOW_BUDGET_CLEANUP.md).


## Wu light numeric layers (2026-10-27)

Separating numeric definitions from their real bridges and grouping original
payment proofs removes 517 effective lines and 86 modules. The complete
4,181-module build and independent acceptance checks pass; precision and
the final theorem are unchanged. [Report](WU_LIGHT_NUMERIC_LAYERS.md).


## Li–Liu endpoint positivity, scales and labelled atoms (2026-10-27)

The S1 carrier provides shared exact endpoint and logarithmic-integral positivity
proofs. Four consumers reuse them. Floor-scale, quarter-cutoff and large-divisor
statements share their existing proofs. The public labelled strict-product
statement moves upstream; its downstream duplicate and resulting orphaned
positivity proof are removed. Counting all moved proof bodies and callers, the
main tree and Li–Liu closure each save 78 effective lines; Chen's closure is
unchanged. No module or auxiliary Lean probe is added. All old public kinds/types,
constants, numerical precision and final statements are preserved. Complete build,
literal/axiom checks, internal contracts, five kernel replays, full type census,
tests and local Blueprint pass. See the [report](LILIU_ENDPOINT_CLEANUP.md).


## Li–Liu carrier identities, growth and finite fibers (2026-10-27)

Exact prime-carrier filter identities and real-growth estimates are shared across
their original consumers. Two public scale-membership names move upstream and
their duplicate copies are deleted. S4/S5 use Mathlib's existing finite-fiber
bound. Logarithmic limits and cubic coefficient proofs simplify with their
original conditions. The main tree saves 154 effective lines including all moved
proof bodies and imports; no module or auxiliary Lean probe is added. Chen's
closure grows by +22 lines through the shared log-power foundation. All old public
kinds/types, six endpoint statements, grids and numerical precision are retained.
Complete build, literal/axiom checks, internal contracts, five kernel replays,
type census, tests and local Blueprint pass. The historical 2026-10-24 cohort
statistics are restored separately from current totals. See the
[report](LILIU_CARRIER_CLEANUP.md).


## Wu Fourth Bq formula (2026-10-27)

Exact Horner formulas and general rounding proofs remove 12,882 effective
Lean lines while preserving numerical payments and the 1+1.8938 theorem.
The 4,267-module build and independent acceptance checks pass.
See [the report](WU_FOURTH_BQ_FORMULA.md).


## Li–Liu uniform local products and error payments (2026-10-27)

Three copied local-product witnesses now share one theorem with the original
uniform quantifier order. Normalized remainder payments specialize the existing
logarithmic-absorption estimate. The paper-Q prime-factor product uses Mathlib's
identity, and two duplicate private nonnegativity proofs are removed. Counting
the new shared module, production sources save 192 effective lines; no auxiliary
Lean probe is added. All original public kinds/types and six final statements
are preserved. Complete build, literal/axiom probes, prior strengthening contracts,
five kernel replays, type census, script tests and local Blueprint pass. See the
[report](LILIU_PRODUCT_CLEANUP.md).


## Li–Liu shared continuity and scalar bounds (2026-10-27)

Third-interval continuity and logarithmic domination now reuse existing lemmas.
The absolute Euler deviation is nonnegative by its unit term and summability;
three internal positivity statements consequently drop the redundant `Even N`
argument. All callers are updated. The six public Chen/Li–Liu theorem statements
are unchanged. Main production sources save 84 effective lines; the separate
17-line acceptance probe leaves a 67-line net saving when also counted.
Complete build, literal/axiom probes, internal statement contracts, five kernel
replays, type comparison, script tests and local Blueprint pass. See the
[report](LILIU_SHARED_LEMMA_CLEANUP.md).


## Wu Eighth integer payments (2026-10-27)

Exact Horner formulas and general rounding proofs remove 2,481 effective
Lean lines while preserving numerical payments and the 1+1.8938 theorem.
The 4,431-module build and independent acceptance checks pass.
See [the report](WU_EIGHTH_INTEGER_PAYMENTS.md).


## Wu Sixth integer payments (2026-10-27)

Exact Horner formulas and general rounding proofs remove 10,800 effective
Lean lines while preserving numerical payments and the 1+1.8938 theorem.
The 4,459-module build and independent acceptance checks pass.
See [the report](WU_SIXTH_INTEGER_PAYMENTS.md).


## Wu exact integer payments (2026-10-27)

Exact Horner formulas and general rounding proofs remove 5,123 effective
Lean lines while preserving numerical payments and the 1+1.8938 theorem.
The 4,583-module build and independent acceptance checks pass.
See [the report](WU_INTEGER_PAYMENTS.md).


## Li–Liu finite weighted-cell calculus (2026-10-27)

Six grids share integrability and weighted-cell integration lemmas. Liu and B10
share convergence from their original inverse-mesh error bounds. B9 reuses the
existing density, strip-volume and finite-sum lemmas; an empty compatibility
facade retains all imports and loses stale headings. Counting the three new
helpers, main sources save 89 effective lines and the Li–Liu closure saves
54; Chen's shared closure grows by 4 lines. All original public types, numerical
bounds and grids are preserved. Complete build, literal/axiom probes, five kernel
replays, type comparison, script tests and local Blueprint pass. See the
[report](LILIU_GRID_CALCULUS_CLEANUP.md).


## Li–Liu shared analytic foundations (2026-10-27)

Two shared modules collect existing logarithmic-coordinate and harmonic-weight
lemmas; three general rectangle lemmas replace repeated regularity/bound proofs.
The Perron proof imports its actual providers. All original public types and
all thirteen relocated source bodies are preserved. Counting both new modules,
main sources save 11 lines and the Li–Liu closure saves 1,086; Chen's shared
closure grows by 22 lines. Complete build, literal/axiom probes, five kernel
replays, type comparison, script tests and local Blueprint pass. See the
[report](LILIU_LOG_KERNEL_CLEANUP.md).



## Wu Hf4 shared certificates (2026-10-27)

Sharing panel-independent models and deriving exact add/neg/scale certificates
removes 5,404 effective Lean lines and 908,008 bytes while retaining
all 76,200 numerical fields and 40 panel bounds. The 4,643-module build,
literal/axiom checks and six independent kernel replays pass.
See [the report](WU_SHARED_CERTIFICATES.md).


## Wu derived-table and correction compression (2026-10-27)

Derived outer samples, exact C/D recurrences and a shared eighth-correction
soundness theorem remove 20,210 effective Lean lines while preserving
1+1.8938 and every original numerical bound. The 4,641-module build,
literal/axiom checks and independent kernel replays pass.
See [the report](WU_DERIVED_COMPRESSION.md).


## Li–Liu one-sided continuity simplification (2026-10-26)

Five fixed-loss and lower-exponent proofs now use Mathlib's existing one-sided
neighborhood lemmas. The change removes 60 effective lines and 2,201 bytes,
taking main sources to 203,002 lines and the Li–Liu closure to 196,487. The
complete build, literal/axiom probes, five kernel replays, public-type comparison,
script suite and local Blueprint pass. Public statements and constants are
unchanged. A proposed import-branch deletion failed complete verification and
was fully restored, contributing no savings. See the
[follow-up report](LILIU_CONTINUITY_CLEANUP.md).

## Wu cumulative-table and exact-certificate compression (2026-10-26)

Exact integer recurrences replace redundant fourth-slot cumulative values;
shared arithmetic checks remove seventh/ninth point proofs and intermediate
rounding certificates in the sixth gain. This removes 31,655 effective Lean
lines and 61 modules while preserving all original values and bounds. The
4,713-module build, literal/axiom probes and six kernel replays pass.
See [the report](WU_TABLE_COMPRESSION.md).


## Li–Liu cleanup after original-paper comparison (2026-10-26)

Two cleanup waves share the quantitative count across all four public endpoints,
remove weaker duplicate integral certificates and obsolete assemblies, and move
generic sieve factors out of Chen applications. The main tree falls from 233,959
to **203,062 effective lines**, a net saving of **30,897**. Li–Liu's import closure
falls from 219,749 to **196,547 lines**, saving **23,202 (10.56%)**. All moved code
and additions are included. The public mathematical targets remain unchanged.

The complete build, both literal/axiom probes, five public-module kernel replays,
surviving-public-type comparison and local Blueprint validation pass. The script
suite has 115 passes and one optional fixture skip. A fresh post-build pruning
scan is recorded separately. Concurrent Wu reductions are excluded from these
figures. See the [cleanup report](LILIU_CLEANUP.md) and
[source measurements](SOURCE_SIZE.md).

## Wu Hf4 exact-kernel compression (2026-10-26)

An exact Cayley-coordinate rewrite reduces the Hf4 arithmetic DAG from 418 to
381 nodes. Shared rational model checks replace repeated real-arithmetic proofs,
removing 50,995 effective Lean lines with all 40 original panel bounds preserved.
The 4,774-module build, both public statements, standard-axiom checks and five
targeted kernel replays pass. See [the report](WU_HF4_COMPRESSION.md).


## Wu structural simplification (2026-10-26)

The fifth gain now uses the first-order logarithm inequality directly, preserving
all statements and precision. The full source tree loses 9 effective lines; the
final theorem closure loses 425 lines and five imported modules. Full build,
1.8938/1.894 acceptance and targeted kernel replay pass. A separately checked Hf4
polynomial-envelope candidate is retained for future integration, with no claimed
main-proof savings yet. See [the report](WU_STRUCTURAL_SIMPLIFICATION.md).

## Public Wu 1+1.8938 and further compression (2026-10-26)

`WuPaper.ClassicalSlots.one8938` now states the unconditional exact bound
`r^5000 ≤ q^4469`; `one894` remains available. This exposes the already certified
internal exponent without changing the numerical budget. Shared rational checks
compress the C and eighth raw certificates while preserving their payment tables
and quadrature meshes. This phase removes **67,589 effective lines**, bringing
the final closure to **688,336 lines**, a cumulative reduction of **438,300**.

The full 4,771-module build, both literal/axiom probes, four targeted kernel
replays, generator reproduction and compiled interface comparison pass.
See the [report](WU_18938_COMPRESSION.md) for measurements and exact scope.


## Wu certificate compression with precision retained (2026-10-26)

The 1+1.894 proof keeps its internal 1.8938 parameter, all quadrature meshes,
rounding scales and error budgets. Shared exact-rational soundness proofs and
kernel-checked finite blocks replace repeated pointwise proofs. All 11 numeric
tables remain byte-identical. The theorem import closure drops from 1,126,636
to 755,925 effective lines: **370,711 fewer lines (32.90%)**, including four
new helper modules. The complete research inventory drops from 8,826 to 5,441.

Full source/object/dependency validation, the literal/axiom checks, five targeted
kernel replays, generator reproduction and compiled interface comparison pass.
See the [audit](WU_PRECISION_COMPRESSION.md) for exact scope and evidence.


## Finite Selberg proof consolidation after original-paper comparison

The five supplied originals support sharing the finite Selberg optimization
without replacing the analytic obligations by citations. One generic truncated
optimizer now supplies the full-divisor and Liu-source specializations. The
public definitions and quantitative theorem targets remain intact; the new
common module and all moved code are included in the measurements.

This phase saves another **598 effective code lines**, taking the complete main
tree from 234,557 to 233,959 lines. Chen's import closure is 99,189 lines and
Li–Liu's is 219,749; Wu's independent sources are unchanged. Further finite
arithmetic reductions use existing prime-factor identities and division
multiplication. Coprimality screens, weighted remainder bounds and the exact
Chen `0.67` count remain necessary.

The full 2,143-module build, both literal/axiom probes, five public-module
replays and 115 script tests pass; one optional full-export fixture is skipped.
All 11,864 compared public declaration types from the previous main snapshot
match. The local Blueprint render and unchanged Wu receipt checks also pass.
See the [paper comparison](CHEN_PAPER_COMPARISON.md),
[verification](VERIFICATION.md) and [source measurements](SOURCE_SIZE.md).
The earlier sections retain their own source snapshots and measurements.

## Chen 1+2 redundancy removal (2026-10-25)

The main tree removes 392 unused modules and extracts one small primitive
large-sieve helper. Including all moved code and shared-consumer changes, it
falls from 350,143 to **234,557 effective code lines**, a net reduction of
**115,586 lines**. Chen's local import closure falls to 99,787 effective lines
and Li–Liu's to 220,347. The independent Wu research sources are unchanged.

The cleanup removes unused historical moment/contour, q¹ diagnostic and
switching branches, trims unused declarations and implied imports, shares the
unconditional distribution producer, narrows the PNT import route and reuses
the actual `0.67` count to prove existence. It preserves the public Chen and
Li–Liu mathematical targets, noncoprime corrections and repeated-factor
accounting. Unused internal module paths and declarations are intentionally
removed. No build-time speedup or mathematically minimal proof is claimed.

The full 2,142-module build (10,850 Lake jobs), both statement/axiom probes,
five public-module kernel replays and 115 script tests pass; one optional
full-export corruption test is skipped. All 5,302 compared surviving public
declaration types match the original Chen census. Wu source/hash and existing-receipt acceptance
checks pass again. See [verification](VERIFICATION.md), the
[cleanup audit](CHEN_REDUNDANCY_AUDIT.md) and [source measurements](SOURCE_SIZE.md).

## Wu04/Wu08 1+1.894 and shared-proof refactoring (2026-10-24)

The separate [Wu04/Wu08 development](../research/wu2008/README.md) now proves
the unconditional theorem `WuPaper.ClassicalSlots.one894`. Every sufficiently
large even natural number has `N = p + r*q`, with `p` and `q` prime, `r = 1`
or prime, and the exact condition `r^500 ≤ q^447`. The final entry is
[`WR2ClassicalCertificate`](../research/wu2008/src/WR2ClassicalCertificate.lean).
Classical-slot certificates and the double-sieve improvements discharge the
coefficient bound used by the actual representation-count argument.

The complete 8,826-module research source build, independent literal-statement
and axiom checks, and final-module kernel replay over rebuilt imports passed.
The main tree's 2,533 source modules also passed the full default-library build
(11,241 Lake jobs), both Chen/Li–Liu acceptance probes, and five public-module
replays. The reported endpoint axioms are confined to `propext`,
`Classical.choice` and `Quot.sound`. See the [verification guide](VERIFICATION.md)
and [completion record](../research/wu2008/completion-audit.json) for scope.

Chen and Li–Liu proofs now share finite-fibre and representation helpers, and
the S3 rational data is separated from analytic proofs. Relative to
`09b97db5764ade1246bfb77206baa1b124760958`, the refactoring cohort, including
split-out files, saves 129 effective code lines and 8,961 bytes. Including the
other new proof modules, the main tree grows by 1,104 effective lines. The
[source-size report](SOURCE_SIZE.md) gives the three theorem sizes and counting
method. No current build-time speedup is claimed.

The Wu sources retain their separate manifest and build driver; root Lake targets
provide the Chen and Li–Liu interfaces. The accepted Wu endpoint is 1+1.894;
these records do not claim a separate literal acceptance of 1+1.8938.

## Li–Liu 1+1.9

The project now formalizes Li–Liu's 1+1.9 theorem alongside the existing Chen
1+2 development. Every sufficiently large even natural number has a
representation `N = p + r*q`, with `p` and `q` prime, `r = 1` or prime, and
`r^10 ≤ q^9`. A second endpoint gives the equivalent real-power formulation.

The quantitative result counts distinct eligible primes `p` and proves

```text
(1/2500) * (liuSingularSeries(N) * N / log(N)^2) < D19(N)
```

for all sufficiently large even `N`. The coefficient `1/2500` is exactly
`0.0004`. For each fixed real `κ < 515093/800000000`, a further endpoint gives
the eventual non-strict lower bound with coefficient `κ`; its threshold is
chosen after `κ`. [THEOREMS.md](THEOREMS.md) defines the count and the exact
Liu singular-series normalization.

### Imports and existing builds

`Goldbach` retains the 1+2 entry and public names. Import
`Goldbach.OnePlusOneNine` for the four new Li–Liu endpoints, or `Goldbach.All`
for both developments. The package configuration, toolchain and dependency
pins stay fixed. Keep `.lake/` when updating an existing build; Lake can reuse
unchanged dependencies and rebuild the new or affected modules. Use
`lake build Goldbach.Theorem`, `lake build Goldbach.OnePlusOneNine`, or
`lake build Goldbach.All` for the selected public target, and `lake build`
for the full project. The [README](../README.md#focused-builds-and-upgrading-an-existing-checkout)
gives the branch-update commands.

The [verification guide](VERIFICATION.md) separates full source checking,
the separate Chen and Li–Liu acceptance probes, and endpoint inspection. The existing 1+2
verification records retain their original theorem and revision scope.

## Historical release: v1.0.0

The remainder of this page records the **1+2** release, including its source
counts, proof-path changes and measured clean builds.

Compared with **v1.0.0-rc1**, commit
`976e60343f5cc50b2f5b2b980de21124e5afc662`.

The first stable release provides Chen's 1+2 theorem and its eventual `0.67`
representation lower bound, with shared proof infrastructure, a warning-free
build, and a project website linking the mathematical outline and Lean sources.

## Lean source size

Count nonblank physical lines after removing Lean line comments and nested
block comments, including documentation comments. Retain string literals and
code preceding an inline comment. Include root Lean entry files and all Lean
files in the four project source directories, including newly added helpers.
Exclude dependencies, build output, Markdown, tooling, and external optimization
artifacts. The resulting metric is the number of Lean source lines.

| Source area | v1.0.0-rc1 | This revision | Change |
|---|---:|---:|---:|
| Goldbach (including Blueprint metadata) | 55 | 110 | +55 |
| MathlibNt | 201,703 | 192,373 | -9,330 |
| AnalyticNumberTheory | 16,003 | 13,841 | -2,162 |
| PrimeNumberTheoremAnd | 15,477 | 15,076 | -401 |
| Root entry files | 44 | 44 | 0 |
| **Total** | **233,282** | **221,444** | **-11,838 (-5.07%)** |

The Lean source file count changes from **729 to 735**. Five focused helper
modules replace repeated local arguments, and one isolated module annotates
existing declarations for Blueprint. Without its 55 lines of presentation
metadata, the proof source is 221,389 lines, a reduction of 11,893 lines (5.10%).
The total above includes this metadata. Counts compare complete source trees
using one scanner; string literals contribute 33 lines in each tree.

Reproduce the v1.0.0 count from that source revision with
`python3 scripts/check.py --static-only --count-lines`.
The same `count_code_lines` function applied to the Git blobs of `v1.0.0-rc1`
reproduces 233,282. Both totals use the same Lean-only counting scope.

## Proof-path improvements

### Shared estimates

The dependency audit examined 166 groups of structurally identical theorem
types. Of these, 95 required reuse changes, 39 already reused an existing proof,
and 32 were trivial wrappers. Reuse decisions checked import direction,
existing providers, and public interfaces before changing consumers.

Shared logarithmic and scalar estimates now live below their consumers in
[LogPowerBounds](../MathlibNt/Analysis/LogPowerBounds.lean),
[large-sieve LogPowerBounds](../MathlibNt/AnalyticNumberTheory/LargeSieve/LogPowerBounds.lean),
[PanQuotientBounds](../MathlibNt/AnalyticNumberTheory/LargeSieve/PanQuotientBounds.lean),
[SuzukiEndpointScalarBounds](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiEndpointScalarBounds.lean),
and [SuzukiFixedGapRpowMargin](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiFixedGapRpowMargin.lean).
Consumers now share these providers. Public forwarding lemmas remain where they preserve the
existing API.

### One Suzuki fixed-head route

[SuzukiCutoffClaim146iiiSanitized](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiCutoffClaim146iiiSanitized.lean)
now imports
[SuzukiMovingSigmaElementaryHead](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiMovingSigmaElementaryHead.lean)
for `exists_sourceSigma_fixed_lower_threshold`,
`fixedCompactPerturbationContract`, and
`lemma133WeightedHeadContract_corrected`. The duplicate long proof bodies and
their duplicate private support lemmas were removed. The fixed-head provider
still supplies the same public statements; the cutoff logarithmic-domination
argument remains a separate consumer.

The fixed-perturbation convergence theorem is provided from
[SuzukiClaim146Quantitative](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiClaim146Quantitative.lean),
and fixed-gap power estimates use the shared scalar layer. The cutoff and moving-head implementations now use a common acyclic
dependency path.

### Character counts use the common bound

In [VaughanDirectAPNormalizedTypeIIActualPhysical](../MathlibNt/AnalyticNumberTheory/Vaughan/VaughanDirectAPNormalizedTypeIIActualPhysical.lean),
`card_primitiveCharacter_le_totient` now directly applies
`primitiveCharacter_card_le_totient_basic`. The public alias is retained, but
the finite-cardinality argument comes from the common provider.

### Explicit order and algebra steps

The cutoff square-root comparison now uses `le_of_sq_le_sq` with an explicit
power identity. Its logarithmic estimates use `add_le_add` to expose
the exact inequalities being combined.

Further cleanup replaced 44 local automation points across 20 files
in Suzuki, Chen1973, large-sieve, Vaughan, Dirichlet L-function, arithmetic,
switching, and prime-number-theorem modules. Examples include multiplication and division
monotonicity, cancellation with an explicit nonzero premise, square comparison,
and positivity-to-strict-order conversions. Additional moving-head product and
quotient steps use the same approach. Automation remains where it makes the
proof clearer. Build performance is measured by the clean-build benchmark below.

### Public mathematics stays fixed

The literal specification in [Goldbach/Statement.lean](../Goldbach/Statement.lean)
and the public endpoints in [Goldbach/Theorem.lean](../Goldbach/Theorem.lean)
are unchanged from the release candidate. Each public endpoint uses its own implementation declaration, and both share
the proved Liu-Pan distribution input. The implementation discharges the
analytic premises through proved theorems. Public axiom reports contain only
Lean's standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Navigation and dependency views

The README now provides a mathematical roadmap. The
[architecture guide](ARCHITECTURE.md) adds a source-backed import graph,
a shared-declaration example, and grouped source links. The old separate module
guide was merged into that page, removing redundant navigation and historical
file-splitting notes while retaining mathematical explanations and attribution.

LeanArchitect extracts declaration metadata and dependencies; LeanBlueprint
renders mathematical documents and dependency graphs from blueprint data.
The diagrams distinguish mathematical implication, direct imports, and
declaration references. Each view identifies its source and edge convention.

An executable [Blueprint](../Goldbach/Blueprint.lean) now supplies seven selected
nodes and six automatically inferred endpoint edges. Three input nodes explicitly
exclude upstream display dependencies to define the diagram boundary; their Lean
proof dependencies remain intact. The renderer links declarations to the source
positions exported by LeanArchitect, pinned to the Git revision used to render.
CI builds a downloadable `goldbach-blueprint` website artifact after the proof
checks. The project website places this selected-declaration view at
`/blueprint/`, alongside Lean Doc at `/docs/` and the independent homepage at `/`.
See the [build instructions](ARCHITECTURE.md#interactive-blueprint).

The Lean API documentation uses the same doc-gen4 renderer as Mathlib documentation and
covers all four project libraries, with declaration search, source links pinned
to the checked-out revision, and links to external dependency documentation.
Mathlib's external documentation tracks upstream updates; the project's proof
dependency is locked in `lake-manifest.json`. Successful main-branch verification is required before
GitHub Pages deployment. See [DOCUMENTATION.md](DOCUMENTATION.md).

## Verification and performance

The release gates are a full warning-fatal build, literal public statement and
standard-axiom checks, script regression tests, an independent replay of
`Goldbach.Theorem`, and validation of the complete documentation website.
The replay checks `Goldbach.Theorem` against its cached imports. Blueprint checks distinguish the seven
selected nodes and six endpoint edges from the full proof dependency graph.
See [VERIFICATION.md](VERIFICATION.md) for the separate acceptance gates and
isolated reconstruction instructions.

Warnings are treated as build failures.
Cleanup covers unused variables, redundant tactics and simplifier arguments,
deprecated names, and explicitly scoped unused section instances. Where an
unused binder received an underscore prefix, in-tree named-argument consumers
were updated as well. The public theorem statements remain unchanged.

The recorded clean builds took **36:23 for v1.0.0-rc1 and 30:06 for v1.0.0**,
a **17.3% reduction in elapsed time**. Sampled peak proportional memory increased
from **5.97 to 6.85 GiB**; sampled peak resident memory was **10.48 and 10.43 GiB**,
respectively. Each version has one recorded run using the same CPU model and
thread settings. Timing depends on machine load and cache state.

The v1.0.0 run starts from a separate checkout with cached pinned dependencies
and zero compiled project modules. It finishes with zero warnings and matching
proof-source fingerprints before and after the build. The
[benchmark guide](BUILD_BENCHMARK.md) describes the timing and memory methods,
including the recorded sampling failures. Full records are available for
[v1.0.0-rc1](benchmarks/v1.0.0-rc1.json) and [v1.0.0](benchmarks/v1.0.0.json).
