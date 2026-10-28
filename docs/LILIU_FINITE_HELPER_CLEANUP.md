# Li–Liu: finite-sum, logarithmic-payment and grid helpers

This phase starts from the [accepted finite coprimality-gate snapshot](LILIU_GATE_BUDGET_CLEANUP.md):
202,026 main effective lines, a 194,471-line Li–Liu closure and a 99,260-line Chen
closure. Nine existing main-library files change. No module, public declaration
or auxiliary Lean probe is added or deleted. All 10,405 original public names,
kinds and type hashes remain.

## Mathematical changes

The private finite-sum identities in the quadratic explicit Pólya–Vinogradov
estimate and Fouvry completion retain their original names and complete types.
For nonzero modulus `q`, write `q = r+1`, rewrite the range sum with Mathlib's
`Fin.sum_univ_eq_sum_range`, then apply `Finset.sum_congr` and
`ZMod.natCast_zmod_val`. This replaces a manual finite equivalence and a separate
explicit bijection with three-line proof bodies. The original `[NeZero q]`
hypothesis remains, including modulus one; no primality hypothesis is introduced.
The complete character/kernel estimates and their numerical constants are
unchanged. Both helpers actually reference the Mathlib sum and cast theorems.

The public `TransportAbsorption.eventually_log_power_budget` now directly calls
the existing `MathlibNt.Analysis.eventually_const_mul_log_rpow_le_rpow`, with an
explicit import of its provider. The statement remains valid for arbitrary real
`C` and `A` and every `s > 0`. The threshold still precedes the varying real
input. The existing general proof is unchanged; no sign restriction on `C` or
logarithmic exponent `A` is added.

The B8 and B9 private paid-error helpers and the G11 public normalized integral
log-error bound reuse the already established
`LiuWeight.eventually_inverse_log_remainder_le_liuSingularSeries` theorem.
`Real.rpow_ofNat` reconciles real exponent three with its natural-power form;
associativity and division identities reconcile the normalization. Their full
original types remain, including arbitrary signed `C`, positive relative error,
the genuine N-dependent Liu singular series and the original squared-log
normalization. The uniform universal-product lower bound remains in the unchanged
shared producer, rather than being reproved in each consumer. All three actual
compiled proof cones reach that producer.

The existing public `directPayMain_span` statement and complete proof move from
DirectPayMainLocal into KSectionReindex, immediately after the actual
`wKSectionGridUpper` definition. Both consumers already import that provider
transitively. SecondaryLocal retains its original public
`directPaySecondary_grid` name/type and directly calls the moved proof.
The inclusive endpoint `upper+1` is preserved, as are all five independent caps
and the original dyadic upper cutoff `2^(j 1+1)-1`. The provider's previous source
text is otherwise identical. No carrier, grid, mask or finite-sum definition
changes, and no reverse application dependency is introduced.

## Measurements

| Source group | Net effective-line change |
|---|---:|
| Two finite ZMod-sum identities | -12 |
| Existing general real log-power budget | -4 |
| Three Liu singular-series log payments | -12 |
| Shared inclusive grid-endpoint proof | -6 |
| Complete phase | -34 |

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,803 | 1,803 | 0 |
| Main effective lines | 202,026 | 201,992 | -34 |
| Li–Liu closure modules | 1,432 | 1,432 | 0 |
| Li–Liu closure effective lines | 194,471 | 194,437 | -34 |
| Chen closure effective lines | 99,260 | 99,253 | -7 |

All moved code, the retained public aliases, the new direct import and rewritten
calls are counted. Main physical lines change by -29 and UTF-8 bytes
by -1,740. Chen's closure savings come from the quadratic explicit
Pólya–Vinogradov provider. Closure membership is measured from the actual import
graph; names alone do not determine which theorem uses a file. Shared modules
count independently in each theorem closure. External Lake dependencies are
excluded. No proof moves outside the measured main tree. The existing 17-line
internal-strengthening contract is reused without any new auxiliary Lean code.
No minimality or build-speed claim is made.

## Acceptance

All nine gates pass: warning-free 1,803-module full source build (10,511 Lake jobs),
both public literal/axiom checks, unchanged internal-strengthening contracts,
five named-module kernel replays and script tests (115 passes and one optional
full-export fixture skip). Kernel replays cover `Goldbach.Theorem`,
`Goldbach.Checks`, `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and
`Goldbach.All` over rebuilt imports; independent replay of every imported module
is not claimed. All 1,809 main source/configuration/checker pins and the separately
pinned statement probe match after each gate. The source inventory is unchanged.

The complete census preserves all 10,405 original public names/kinds/type hashes,
with no missing or added public declarations. Four explicit private helpers retain
their names and complete kind/type hashes. The existing public grid span moves
upstream with its statement unchanged, and the secondary grid proof actually
reaches it. All nine complete-file prototypes passed warning-as-error compilation
before application; matching source/log fingerprints were rechecked. Grid consumer
prototypes include the actual moved proof, not a forward assumption. The PV
prototype emits an informational `ring_nf` suggestion from the complete file;
its actual compiler process exits zero, without warnings or errors. Earlier
isolated ZMod conversion drafts failed elaboration; only the successful
three-line proof is used. Full production combination acceptance is separate
from the historical prototype receipts.

All six public endpoints retain their exact constants and quantifier order:
`D19`, prime conditions, `r^10 ≤ q^9`, the genuine real exponent, Liu's singular
series, strict `1/2500`, fixed `κ < 515093/800000000` before the threshold and
Chen's `0.67`. Public axioms remain only `propext`, `Classical.choice` and
`Quot.sound`. The final producer guard, all original numerical grids, precision,
error constants and release checks are unchanged. Fresh Blueprint extraction,
local rendering, source positions, graph, annotations and tests pass:
68 nodes, 120 edges, four chapters and all six original exits.

This is an uncommitted local snapshot. Separate concurrent `research/wu2008`
sources, certificates and documentation are outside this phase. Historical
source-size cohorts remain separate from current totals.

See [validation](../research/liliu-finite-helper-cleanup/validation.json),
[pinned inputs](../research/liliu-finite-helper-cleanup/validation-inputs.json),
[type preservation](../research/liliu-finite-helper-cleanup/type-preservation.json),
[nine-file changes](../research/liliu-finite-helper-cleanup/changes.json),
[retained private statements](../research/liliu-finite-helper-cleanup/retained-private-statements.json),
[moved grid proof](../research/liliu-finite-helper-cleanup/moved-public-proofs.json),
[actual shared-proof references](../research/liliu-finite-helper-cleanup/shared-proof-references.json),
[source sizes](../research/liliu-finite-helper-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-finite-helper-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-finite-helper-cleanup/reproduce.py --output /tmp/liliu-finite-helper-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` requests separate checks of a stable rebuilt Wu tree.
Unimplemented follow-up candidates are excluded from the savings above.
