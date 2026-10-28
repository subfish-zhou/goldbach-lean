# Li–Liu 1+1.9 cleanup

This records the first two accepted waves. The latest
[continuity follow-up](LILIU_CONTINUITY_CLEANUP.md) saves another 60 lines.

This report records the implementation following the
[original-paper audit](LILIU_REDUNDANCY_AUDIT.md). The baseline is the accepted
2,143-module / 233,959-effective-line main tree, with a 219,749-line Li–Liu import
closure. It includes the earlier Chen cleanup. The current sources are an
uncommitted working-tree snapshot; the checkout base is not a deployment record.

## One quantitative argument, four public endpoints

The original article concludes with its quantitative count in Section 5.5.
The natural-power existence theorem now follows directly from the strict count
and `D19_pos_iff`. The real-power theorem follows from the same witnesses through
the existing exact exponent conversion. The stronger fixed-coefficient family
uses the same author-G11 ledger. This removes the older, weaker positivity route.

The G67 integral certificates move into
[`LiLiuGoldbachG67IntegralCertificate.lean`](../MathlibNt/SieveTheory/LiLiuGoldbachG67IntegralCertificate.lean),
so the quantitative assembly no longer depends on its qualitative consequence.
The four public statements retain the actual distinct-prime count `D19`,
`r^10 ≤ q^9`, the Liu singular-series normalization, the strict `1/2500` count
and the order of quantifiers selecting fixed `κ < 515093/800000000` before the
threshold. No additional analytic premise is introduced.

## First cleanup wave

The stronger S4 and B10 retained-endpoint certificates keep their actual
polynomial, derivative, substitution and integral proofs. Their weaker duplicate
certificates are removed. Obsolete scalar wrappers, intermediate ledgers,
unconsumed branches and repeated diagnostic modules are deleted using compiled
type/value/recursor references together with source references needed for
elaboration. Shared Chen dependencies and selected Blueprint declarations are
protected. Required local notation registrations and command wrappers remain.

The final reachability check now inspects the four actual public proof terms
and their quantitative producers. The independent literal-statement and axiom
probes remain unchanged. Retired build objects are moved outside the import path
before rebuilding.

[First-wave validation](../research/liliu-cleanup/wave1-validation.json) accepts
1,800 main modules and 204,151 effective lines: **29,808 fewer main lines**.
The Li–Liu closure becomes 1,438 modules / 199,763 lines, a saving of 19,986.
All 10,451 surviving public types match, with intentional internal deletions
listed explicitly. Independent kernel replays and the full script suite are
reserved for the final combined snapshot.

## Second cleanup wave

A fresh census after the accepted first wave identifies three more obsolete
modules and additional unused declaration blocks. Repeated direct imports are
removed where another retained import already supplies the same module.

The shared explicit lower-sieve factor and its inner integral move to
[`DimensionOneLowerFactor.lean`](../MathlibNt/SieveTheory/LinearSieve/DimensionOneLowerFactor.lean).
One continuity proof on `[4,6]` supplies both Chen's value `5` and Li–Liu's value
`33/8`. The former duplicated Li–Liu continuity proof becomes a specialization.
Existing public definitions and theorem types are retained.

The explicit upper factor and generic upper fundamental-lemma interface move
from Chen application files into
[`DimensionOneUpperFactor.lean`](../MathlibNt/SieveTheory/LinearSieve/DimensionOneUpperFactor.lean).
This preserves their statements while removing application dependencies from
the generic upper-sieve producer.

Generic Suzuki prime sums, the elementary boundary estimate and the Richert
weight-payment argument now import their actual generic providers. This removes
unnecessary paths through Chen applications. Consumers requiring Chen-specific
material import it explicitly. The finite sums, distribution payment and analytic
inequalities keep their original proof obligations.

## Measurement and acceptance

| Scope | Before cleanup | After wave 1 | After wave 2 | Total saving |
|---|---:|---:|---:|---:|
| Main effective lines | 233,959 | 204,151 | 203,062 | 30,897 |
| Li–Liu import-closure effective lines | 219,749 | 199,763 | 196,547 | 23,202 (10.56%) |
| Main modules | 2,143 | 1,800 | 1,799 | 344 |
| Li–Liu import-closure modules | 1,521 | 1,438 | 1,435 | 86 |

Wave 2 saves another 1,089 main lines and 3,216 Li–Liu closure lines. Across
both waves, 347 old main modules are deleted and three common modules added.
Moved code and all additions are included. The second wave adds 38 lines to
Chen's closure through the shared factors and interval theorem; its net change
from the pre-cleanup snapshot is +37 lines. Current Chen: 527 modules / 99,226
effective lines. Import closures overlap and must not be added. These are whole
module source sizes, excluding external Lake dependencies, rather than minimal
proof-term lengths. [Complete size record](../research/liliu-cleanup/source-size.json).

The final warning-free build passes all **1,799 modules / 10,507 Lake jobs**.
Both independent public literal/axiom probes pass, as do kernel replays of
`Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All`. All 116 script tests are
accounted for: 115 pass, with one optional full-export fixture test skipped.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted by the public
axiom probes. These are named-module kernel replays over the built imports;
a separate replay of every import is not claimed.

The [type comparison](../research/liliu-cleanup/type-preservation.json) checks
10,385 surviving public declaration kinds/type hashes against the complete
pre-cleanup main census, with no mismatches. It explicitly lists 1,481
intentional internal public deletions and the additions. Four relocated core
mathematical definitions are also
[byte-identical](../research/liliu-cleanup/moved-definitions.json).
The six public Chen/Li–Liu endpoint statements are protected independently by
the literal probes. Source inventory and fingerprints match after each gate.

The local Blueprint is freshly extracted, rendered and checked: **68
nodes / 120 edges**, four chapter graphs and the six original public
exits. Source positions refer to current extraction artifacts. This is a local
render of the uncommitted sources, with no deployment implied.
[Blueprint evidence](../research/liliu-cleanup/blueprint-validation.json).

The [next-wave scan](../research/liliu-cleanup/next-wave-scan.json) runs again
against the newly built declarations and elaboration references. It records
0 additional module candidates,
0 unused declaration blocks and
0 implied direct imports under the
same conservative pruning rule. Shared consumers, exact power conversions,
selected Blueprint declarations and required notation/tactic registrations stay
protected. This is convergence of that rule, not a claim of mathematical
minimality or an audit of every bibliography dependency.

The [validation record](../research/liliu-cleanup/validation.json),
[pinned proof inputs](../research/liliu-cleanup/validation-inputs.json),
[dependency census](../research/liliu-cleanup/analysis.json) and
[per-wave changes](../research/liliu-cleanup/changes.json) identify the accepted
snapshot. Raw build logs and compiled objects remain local; their hashes are
recorded. Reproduce the main acceptance queue after dependency setup with:

```sh
python3 research/liliu-cleanup/reproduce.py --output /tmp/liliu-recheck
python3 research/liliu-audit/reproduce.py --output /tmp/liliu-census
python3 research/liliu-cleanup/scan_redundancy.py --census /tmp/liliu-census --output /tmp/liliu-rescan
python3 research/liliu-cleanup/measure_main.py
```

Use fresh output paths. The census/scan reports describe candidates without
editing production sources. See the standard Blueprint rendering instructions
in [documentation](DOCUMENTATION.md) for the independent local render.

Concurrent Wu compression has its own [accepted report](WU_HF4_COMPRESSION.md).
While this main acceptance ran, another task started changing the ninth-term
certificate. The optional Wu receipt/literal check therefore failed on a changed
source hash and is recorded separately, without being counted as a success.
The latest separately accepted Wu snapshot is linked; the current in-progress
Wu tree is outside this main-library acceptance. No fresh full Wu build or Wu
kernel replay is claimed here. Wu reductions do not contribute to the main or
Li–Liu savings above. This phase translates new Wu release prose into English
for the unchanged release-language gate, preserving its mathematical content;
it does not edit the separate Wu research proof sources or numerical tables.
