# Li–Liu: endpoint positivity, floor scales and labelled atoms

This phase starts from the [accepted carrier/growth snapshot](LILIU_CARRIER_CLEANUP.md):
1,802 main modules / 202,472 effective lines, a 194,917-line Li–Liu closure and
a 99,246-line Chen closure. Thirteen existing modules change. No production
module or auxiliary Lean probe is added. All original public names, kinds and
type hashes are preserved. One existing public strict-product theorem moves
upstream with its original statement and docstring.

## Mathematical changes

The actual S1 carrier now provides `goldbachS1Endpoint_two_le` under the original
`4 ≤ N` and `ε < 2/15` hypotheses, and the corresponding nonnegativity of the
original genuine logarithmic integral. The endpoint is still exactly
`Nat.ceil ((1 - ε) * N) - 1`; no floor/ceiling or strict-endpoint convention changes.
S3PaidUpper, S3NormalizedUpper, CompositeMovingCount and PairMovingKernel reuse
these proofs instead of independently proving the same ceiling geometry.
The integral retains the original normalization `2 / log 2`. The moving-count
proof still covers the branch `t < 2` using count nonnegativity, with its full
literal Rosser remainder and threshold order.

The existing floor-scale estimate `2m ≤ Y` under `Y ≥ 8` and
`m ≤ Y^(2/3)` is exposed in MainWeight, and ContinuousMain deletes its exact
private duplicate. The S2 quarter-cutoff threshold is similarly exposed in
S2PaidUpper and reused by S2NormalizedUpper, preserving `K > 0`, `N₀ ≥ 4`,
the exponent `1/4` and every quantifier. ErrorFoundations exposes the exact
zero-count statement for a divisor larger than the entire positive carrier;
WeightInitialBudget deletes its copy. The conditions `1 ≤ n < N`, `N < d`
and all `literalH` parameters remain unchanged.

The existing public `goldbachB10Atom_prod_lt` name moves from B10Congruence to
Pi10Sifted, replacing an equivalent private proof. Its genuine labelled Sigma
carrier and strict `mq < N` conclusion are unchanged. The docstring moves with
it, and downstream imports reuse the same public name. The downstream private
positivity helper then has no remaining consumer and is removed. Its original
sole compiled consumer is the moved public theorem. The upstream positivity
helper is retained, has the same kind/type hash, and is verified reachable from
the moved proof. Its other consumers remain intact.

`S3LiEulerUpper_endpoint_large` is unchanged: it allows the larger `ε < 1`
domain, arbitrary `X` and an eventual threshold. It is not replaced by the
pointwise `ε < 2/15` theorem. S1PaidLower and S1BetaPaidLower already reuse their
established main-mass result through thin calls and are unchanged.

| Source group | Net effective-line change |
|---|---:|
| Floor-scale estimate and caller | -15 |
| Labelled strict-product proof and resulting orphan | -19 |
| Quarter-cutoff threshold and callers | -13 |
| Large-divisor zero count and caller | -10 |
| Shared endpoint/integral positivity and four consumers | -21 |
| Total | -78 |

## Measurements

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,802 | 1,802 | +0 |
| Main effective lines | 202,472 | 202,394 | -78 |
| Li–Liu closure modules | 1,431 | 1,431 | +0 |
| Li–Liu closure effective lines | 194,917 | 194,839 | -78 |
| Chen closure effective lines | 99,246 | 99,246 | +0 |

All moved proof bodies, five new public statements and rewritten callers are
included. In particular the 14 effective lines added to S1Carrier are counted.
Main physical lines change by -77; UTF-8 bytes change by
-4,110. The main import statements are unchanged. The existing
17-line internal-statement probe is reused unchanged, with no new auxiliary
Lean file. No production proof is moved outside the measured tree. Shared
modules count independently in each theorem closure; the rows must not be added.
External Lake dependencies remain excluded. No smallest-proof or speedup claim
is made. Concurrent Wu research sources and numerical certificates are excluded.

## Acceptance

All nine gates pass: complete warning-free 1,802-module build (10,510 Lake jobs),
both public literal/axiom probes, unchanged internal-strengthening contracts,
five named-module kernel replays and the script suite (115 passes, one optional
full-export fixture skip). Replays cover `Goldbach.Theorem`, `Goldbach.Checks`,
`Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`
over rebuilt imports; separate replays of every imported module are not claimed.

All 1,808 main source/configuration/checker fingerprints and the separately pinned
existing statement probe match after every gate. The fresh complete census
preserves all 10,399 old public kinds/type hashes, with no missing names or
changed types. Five helpers are added: the floor-scale, quarter-cutoff and
large-divisor statements, and the two endpoint positivity statements. The existing
public strict-product name is retained with the same type and verified upstream
owner. Private and specified generated names are excluded from the public count.

Eleven old private names disappear. Ten replacement statements have matching
original kind/type hashes. One newly orphaned downstream positivity proof is
removed after checking its former sole consumer, the retained upstream analogue,
and actual reachability of that analogue from the moved public theorem. This
is not a claim of eleven independently redundant proof bodies: some existing
proofs are exposed or moved, and their duplicate copies are removed. All thirteen
full-file prototypes passed warning-as-error compilation before application;
no forward assumptions or axioms were introduced into those probes.

The six public endpoints retain their exact constants, original prime conditions,
`D19`, `r^10 ≤ q^9`, genuine real exponent, Liu singular-series normalization,
strict `1/2500`, fixed `κ < 515093/800000000` before the threshold and Chen's
`0.67` count. The three unconditional internal Euler positivity statements are
rechecked. Public axioms remain limited to `propext`, `Classical.choice` and
`Quot.sound`. Final producer reachability, every numerical grid, precision and
release check are preserved.

The fresh local Blueprint has 68 nodes, 120 edges, four chapters and all
six original exits, with verified source positions, graph and annotations.
This is an uncommitted local snapshot, not a deployment. Historical source-size
cohort statistics remain separate from current whole-main totals.

See [validation](../research/liliu-endpoint-cleanup/validation.json),
[pinned inputs](../research/liliu-endpoint-cleanup/validation-inputs.json),
[type preservation](../research/liliu-endpoint-cleanup/type-preservation.json),
[thirteen-file changes](../research/liliu-endpoint-cleanup/changes.json),
[private redirects and orphan](../research/liliu-endpoint-cleanup/private-proof-redirects.json),
[moved public proof](../research/liliu-endpoint-cleanup/moved-public-proofs.json),
[source sizes](../research/liliu-endpoint-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-endpoint-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-endpoint-cleanup/reproduce.py --output /tmp/liliu-endpoint-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. The default checks cover the main tree only;
`--include-wu` explicitly requests separate checks of a stable rebuilt Wu tree.
No saving from unimplemented follow-up candidates is included here.
