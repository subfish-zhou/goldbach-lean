# Li–Liu: one-sided continuity proof simplification

This follow-up starts from the [accepted two-wave cleanup](LILIU_CLEANUP.md):
1,799 main modules / 203,062 effective lines, with a 196,547-line Li–Liu import
closure. It simplifies five proofs using existing Mathlib results. No main
modules are added or deleted, and all public mathematical interfaces are retained.

## The mathematical change

Continuity gives an eventual bound near zero. Intersecting it with a positive
upper cutoff and applying `Filter.Eventually.exists_gt` chooses a strictly
positive loss directly. For a lower exponent below a positive endpoint,
`Filter.Eventually.exists_lt` supplies the corresponding left-hand choice.
These standard order-neighborhood lemmas replace repeated choices of a metric
radius, a minimum with half that radius, and separate distance estimates.

The S2 logarithmic difference also uses `fun_prop` to combine its two continuous
logarithms. The original interval hypotheses still discharge both nonzero
conditions. Each proof fixes its tolerance before choosing the small parameter;
the integer threshold remains later in the argument.

| Source module | Effective lines removed, including the added import |
|---|---:|
| `LiLiuGoldbachG11AuthorFinalScalar` | 5 |
| `LiLiuGoldbachG12ClippedUniform` | 6 |
| `LiLiuGoldbachPairIntegralLedger` | 8 |
| `LiLiuGoldbachG12ThinIntegralBudget` | 3 |
| `LiLiuGoldbachS2MainMassUpper` | 38 |
| **Total** | **60** |

The change also removes 60 physical lines and 2,201 UTF-8 bytes. Main sources
now contain **203,002 effective lines**; the Li–Liu closure contains **196,487**.
Chen remains at 99,226 lines. These are complete local source/import-closure
measurements, including the five new external import commands and excluding
external Lake dependencies. No proof-term minimality or speedup is claimed.

## Rejected import-removal experiment

A module-local scan found 246 potential unused imports. Of sixteen priority
single-import probes, thirteen compiled; fifteen combined source probes also
compiled after resolving purely local context requirements. This did not
establish that downstream consumers could lose the re-exported theorems.

The proposed removal of 165 modules failed the complete build. All 165 contained
references used by the accepted final proof terms, including actual analytic
bounds. Every candidate import edit and module deletion was rolled back before
applying the five continuity rewrites. The source inventory is unchanged.
Modules outside those five approved rewrites match the baseline fingerprints;
the [experiment record](../research/liliu-continuity-cleanup/rejected-import-experiment.json)
identifies the restored modules and subsequent approved proof edits explicitly.
**No savings from that rejected branch deletion are counted.**

This distinguishes compilation of one module from acceptance of the complete
proof. Further large savings remain unproven; this result does not establish
mathematical minimality.

## Acceptance

The warning-free build passes all **1,799 modules / 10,507 Lake jobs**. Both
public literal-statement/axiom probes and independent kernel replays of
`Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All` pass. The script suite has
115 passes and one optional full-export fixture skip. All **10,386 public
declaration kinds/type hashes** match the preceding accepted complete main
census, with no missing or added public declarations. Private and specified
generated names are excluded from that comparison.

The four Li–Liu statements retain `D19`, `r^10 ≤ q^9`, the Liu normalization,
the strict `1/2500` count, and fixed `κ < 515093/800000000` before the threshold.
Both Chen statements, including its `0.67` count, also remain unchanged. The
public axiom probes allow only `propext`, `Classical.choice` and `Quot.sound`.
Named-module kernel replays use the built imports; a separate replay of every
import is not claimed.

The Blueprint is freshly extracted and locally rendered: **68 nodes / 120
edges**, four chapter graphs and all six public exits. Current source positions
are verified against the extraction. This is an uncommitted source snapshot;
the checkout base is not a deployment record.

See the [validation](../research/liliu-continuity-cleanup/validation.json),
[pinned inputs](../research/liliu-continuity-cleanup/validation-inputs.json),
[type comparison](../research/liliu-continuity-cleanup/type-preservation.json),
[five-file changes](../research/liliu-continuity-cleanup/changes.json),
[source sizes](../research/liliu-continuity-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-continuity-cleanup/blueprint-validation.json).
After setting up dependencies, reproduce the main queue with a fresh output path:

```sh
python3 research/liliu-continuity-cleanup/reproduce.py --output /tmp/liliu-continuity-recheck
python3 research/liliu-cleanup/measure_main.py
```

Concurrent separate Wu research changes are outside this main acceptance.
The new Wu table-compression release document and the Hf4 historical notice are
translated into English to satisfy the existing unchanged release-language gate;
their formulas, numbers and mathematical content are preserved. This phase makes
no changes to separate Wu research proof sources or numerical certificates.
