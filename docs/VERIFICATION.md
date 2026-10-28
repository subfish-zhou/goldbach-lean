# Verification

Run all commands at the project root with the pinned toolchain:

```sh
unset LEAN_PATH LEAN_SRC_PATH
lake exe cache get
lake --wfail build
python3 scripts/check.py
lake env leanchecker --verbose Goldbach.Theorem
```

For a focused build use `lake build Goldbach.Theorem` (1+2),
`lake build Goldbach.OnePlusOneNine` (1+1.9), or `lake build Goldbach.All`
(both interfaces). Keep `.lake/` during upgrades so Lake can reuse unchanged
artifacts; see the [upgrade instructions](../README.md#focused-builds-and-upgrading-an-existing-checkout).

`python3 scripts/check.py` runs both acceptance probes. The option
`--one-two-only` runs the original Chen probe while retaining the full source
scan. The Li–Liu probe is `Goldbach/OnePlusOneNineChecks.lean`.

The [Wu04/Wu08 development](../research/wu2008/README.md) has a separate source
manifest and build driver. Its accepted endpoint is
`WuPaper.ClassicalSlots.one8938`, with the exact condition `r^5000 ≤ q^4469`;
the legacy `one894` statement is also checked.
Run `python3 build.py --all --jobs 1 --lean-threads 2` and
`python3 check_classical.py` from `research/wu2008` after setting up its pinned
dependencies. The research README gives the final module replay command.
Its 4142-module source build, independent literal statement and standard-axiom
checks, and replay of `WR2ClassicalCertificate` over the rebuilt imports have
passed. The root Lake targets and `scripts/check.py` cover Chen and Li–Liu;
the research gates supply the Wu acceptance evidence. The current
[LiuPan pruning audit](../research/wu-liupan-pruning-audit/validation.json) records
3,165 fresh isolated compilations plus 977 verified unchanged dependencies, followed
by full production receipt verification. Standalone `leanchecker` must set
`LEAN_SYSROOT` to the pinned compiler prefix; see the research README command.

## Accepted shared finite-prefix and divisor proofs (2026-10-27)

All nine gates pass: warning-free 1,803-module full build (10,511 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,809 main
pins and the unchanged auxiliary probe match. All 10,408 old public names/kinds/type
hashes remain; one existing private cardinality theorem becomes public. Compiled
references verify its three consumers, WF's two canonical wrappers and the canonical
sum's Mathlib dependency, with no reverse dependency into WF. Complete-file byte
comparisons limit changes to the identified proofs and visibility. All four imports,
rounded definitions, parity/cubic tests, six endpoints and producer guards remain
unchanged. Blueprint: 68 nodes, 120 edges, four chapters, six exits.
Main/Li–Liu save 66 effective lines; Chen saves 49. See the
[report](LILIU_FINITE_PREFIX_CLEANUP.md) and
[validation](../research/liliu-finite-prefix-cleanup/validation.json).
The following sections retain their historical accepted snapshots.

## Accepted shared calculus and author-weight proofs (2026-10-27)

All nine gates pass: warning-free 1,803-module full build (10,511 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,809 main
pins and the existing auxiliary probe match. All 10,406 old public names/kinds/type
hashes remain. Two G11 private proofs are promoted; duplicate G12 copies are
removed, with exact replacement kinds/type hashes for all four old statements.
All five original analytic consumers reach the shared proofs. Both private complex
shift statements retain their names/types and reach Complex.cpow_add. The existing
global weight cap moves to its definition provider; G12 keeps its original alias.
All nine import lists are identical. Six final statements, producer checks, grids
and precision remain unchanged. Fresh local Blueprint: 68 nodes, 120 edges,
four chapters and six exits. Main/Li–Liu save 27 effective lines; Chen saves 6.
See the [report](LILIU_SHARED_CALCULUS_CLEANUP.md) and
[validation](../research/liliu-shared-calculus-cleanup/validation.json).
The following sections retain their historical accepted snapshots.

## Accepted shared quartic-log remainder payment (2026-10-27)

All nine gates pass: warning-free 1,803-module full build (10,511 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,809 main
pins and the existing auxiliary probe match. All 10,405 old public names/kinds/type
hashes remain. One shared quartic theorem is added; both removed private statements
have exactly its kind/type hash, and both original normalized-upper producers
actually reach it. The canonical provider's original cubic inverse-log proof is
unchanged. Six final statements, producer checks, grids and precision are unchanged.
Fresh local Blueprint: 68 nodes, 120 edges, four chapters and six exits.
Main/Li–Liu save 16 effective lines; Chen's source closure grows by 16 through the
shared provider. Neither Chen public proof cone reaches the new helper. See the
[report](LILIU_QUARTIC_LOG_CLEANUP.md) and
[validation](../research/liliu-quartic-log-cleanup/validation.json).
The following sections retain their historical accepted snapshots.

## Accepted shared boundary-integral and low-positivity proofs (2026-10-27)

All nine gates pass: warning-free 1,803-module full build (10,511 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,809 main
pins and the existing auxiliary probe match. All 10,405 original public names,
kinds and type hashes remain. Four private indicator/majorant stages disappear,
each with exactly one original consumer inside its provider. Compiled reference
cones verify the existing common excess-cover theorem, all seven exact strip-area
producers, original caps/local errors/covers and actual weighted-source integrability.
The public unconditional G9 positivity name/proof moves upstream; the second
public positivity name reuses it with its original type. Final statements,
producer checks, numerical grids, precision and error constants remain unchanged.
Fresh local Blueprint: 68 nodes, 120 edges, four chapters and six exits.
Main/Li–Liu save 127 effective lines; Chen's complete closure totals are unchanged.
See the [report](LILIU_BOUNDARY_INTEGRAL_CLEANUP.md) and
[validation](../research/liliu-boundary-integral-cleanup/validation.json).
The following sections retain their historical accepted snapshots.

## Accepted finite-sum, log-payment and grid helpers (2026-10-27)

All nine gates pass: warning-free 1,803-module full build (10,511 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,809 main
pins and the existing auxiliary probe match. All 10,405 original public names,
kinds and type hashes remain. Four explicit private helpers keep their names and
complete types. The existing inclusive-grid span name moves upstream; the second
public grid alias actually uses it. Actual compiled references verify the shared
Mathlib sums, generic log-power budget and genuine Liu log-remainder producer.
Final statements, original producer checks, numerical grids and precision are
unchanged. Fresh local Blueprint: 68 nodes, 120 edges, four chapters and six exits.
Main/Li–Liu save 34 effective lines; Chen saves 7. See the
[report](LILIU_FINITE_HELPER_CLEANUP.md) and
[validation](../research/liliu-finite-helper-cleanup/validation.json).
The following sections retain their historical accepted snapshots.

## Accepted shared finite coprimality-gate budgets (2026-10-27)

All nine gates pass: warning-free 1,803-module full build (10,511 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,809 main
pins and the existing auxiliary probe match. All 10,405 old public names/kinds/type
hashes remain, with no new public declarations. Four existing general proofs move
to one common provider; B10 reaches its actual shared gate at `K=2`, preserving
its exact public type and `4*T/b` constant. Five old private proof stages are
removed, and both support bounds retain their types. Final statements, original
producer checks and all numerical precision remain unchanged. Fresh local Blueprint:
68 nodes, 120 edges, four chapters and six exits. Main/Li–Liu save 181 effective
lines; Chen's complete closure totals remain unchanged. See the
[report](LILIU_GATE_BUDGET_CLEANUP.md) and
[validation](../research/liliu-gate-budget-cleanup/validation.json).
The following sections retain their historical accepted snapshots.

## Accepted shared low-conductor budgets and Pan maxima (2026-10-27)

All nine gates pass: warning-free 1,802-module full build (10,510 jobs), public
literal/axiom checks, unchanged internal-strengthening contracts, five named kernel
replays and script tests (115 passes, one optional fixture skip). All 1,808 main
pins and the existing auxiliary probe match. All 10,404 old public kinds/type
hashes are identical; only the shared Pan maximum theorem is added. The existing
budget name moves upstream, with actual compiled use by both differently scoped
low-conductor estimates and real-endpoint transport. Seven private names disappear:
five exact replacement types, two residue proofs inlined. The retained private
squarefree statement keeps its type. Six final statements, grids and precision
are unchanged. Fresh local Blueprint: 68 nodes, 120 edges, four chapters, six exits.
Separate Wu research work is excluded; the main-library Wu2004MeanValue modules
are genuine Li–Liu dependencies. See the [report](LILIU_LOW_BUDGET_CLEANUP.md) and
[validation](../research/liliu-low-budget-cleanup/validation.json).
The following main sections retain their historical accepted snapshots.

## Accepted endpoint positivity, scales and labelled atoms (2026-10-27)

All nine gates pass: complete warning-free 1,802-module build (10,510 jobs),
public literal/axiom checks, unchanged internal-strengthening contracts, five named
kernel replays and script tests (115 passes, one optional fixture skip). All
1,808 main pins and the existing auxiliary probe match. All 10,399 old public
kinds/type hashes remain identical; five shared helpers are added. The existing
public strict-product name moves upstream without a type change. Ten private
statements are exposed/shared/moved with matching replacement types; a further
private positivity proof is removed after its sole consumer moves upstream and
uses the retained analogue. The six final statements, grids and precision are
preserved. Fresh local Blueprint: 68 nodes, 120 edges, four chapters and six exits.
Separate Wu work is excluded. See the [report](LILIU_ENDPOINT_CLEANUP.md) and
[validation](../research/liliu-endpoint-cleanup/validation.json).
The following main sections retain their historical accepted snapshots.

## Accepted carrier identities, growth and finite fibers (2026-10-27)

All nine gates pass: full warning-free 1,802-module build (10,510 Lake jobs),
public literal/axiom checks, unchanged internal-strengthening contracts, five named
kernel replays and script tests (115 passes, one optional fixture skip).
All 1,808 main pins and the existing auxiliary probe match. All 10,394 old public
kinds/type hashes remain identical; only four carrier identities and one general
growth estimate are added. Two existing public Gram names move upstream without
type changes. Thirteen old private names disappear after sharing/exposure/movement
or direct Mathlib reuse; their previous compiled consumers were confined to their
own providers. The six final theorem statements and all numerical precision are
preserved. The fresh local Blueprint has 68 nodes, 120 edges, four chapters
and six exits. Separate Wu work is excluded. See the
[report](LILIU_CARRIER_CLEANUP.md) and
[validation](../research/liliu-carrier-cleanup/validation.json).
The following main sections retain their historical accepted snapshots.

## Accepted uniform local products and error payments (2026-10-27)

All nine gates pass: the warning-free 1,802-module build (10,510 Lake jobs),
both public literal/axiom probes, the unchanged internal-strengthening probe,
five named-module kernel replays and the script suite (115 passes, one optional
fixture skip). All 1,808 main pins and the existing auxiliary probe match after
each gate. All 10,393 original public kinds/type hashes match with no missing
names; only the shared uniform local-product witness is added. Five private
proofs are removed after verifying their replacement types and redirecting all
local calls. The six public endpoint statements are unchanged. The fresh local
Blueprint has 68 nodes, 120 edges, four chapters and six exits.
Separate Wu research changes are excluded. See the
[report](LILIU_PRODUCT_CLEANUP.md) and
[validation](../research/liliu-product-cleanup/validation.json).
The following main sections describe their historical accepted snapshots.

## Accepted shared continuity and scalar bounds (2026-10-27)

All nine gates pass: the warning-free 1,801-module build (10,509 Lake jobs), both
public literal/axiom probes, the internal strengthening probe, five named-module
kernel replays and the script suite (115 passes, one optional fixture skip).
All 1,807 main pins plus the separately pinned auxiliary probe match after each
gate. All 10,392 original public names remain; 10,389 kind/type hashes match,
and exactly three internal positivity statements are strengthened by removing
`Even N`. The probe checks their unconditional statements and old-premise
consequences. One unchanged private continuity lemma becomes public. The six
Chen/Li–Liu public exits retain all original statements and constants.
The fresh Blueprint has 68 nodes, 120 edges, four chapters and six exits.
Separate Wu research changes are excluded. See the
[report](LILIU_SHARED_LEMMA_CLEANUP.md) and
[validation](../research/liliu-shared-lemma-cleanup/validation.json).
The following main sections describe their historical accepted snapshots.

## Accepted finite weighted-cell calculus (2026-10-27)

The warning-free 1,801-module main build (10,509 Lake jobs), both literal/axiom
probes, five independent named-module kernel replays and the script suite
(115 passes, one optional fixture skip) pass. All 1,807 pinned inputs match
after every gate. All 10,389 original public kind/type hashes match; only three
generic integration/convergence helpers are added. The nine modified files retain
every original public declaration and every compatibility-facade import.
The fresh local Blueprint has 68 nodes, 120 edges, four chapters and six exits.
Separate concurrent Wu research changes are excluded. See the
[report](LILIU_GRID_CALCULUS_CLEANUP.md) and
[validation](../research/liliu-grid-calculus-cleanup/validation.json).
The following main sections describe their historical accepted snapshots.

## Accepted shared log/harmonic foundations (2026-10-27)

The warning-free 1,801-module main build (10,509 Lake jobs), both
literal/axiom probes, all five named-module kernel replays and the script suite
(115 passes, one optional fixture skip) pass. All 1,807 pinned inputs match after
every gate. All 10,386 original public kind/type hashes are unchanged; only three
generic rectangle helpers are added. Thirteen moved public declarations preserve
their original source bodies. The fresh local Blueprint retains 68 nodes,
120 edges, four chapters and six public exits. Separate concurrent Wu
research changes are outside this main acceptance. See the
[report](LILIU_LOG_KERNEL_CLEANUP.md) and
[validation](../research/liliu-log-kernel-cleanup/validation.json).
The following main sections retain their preceding historical snapshots.

## Accepted one-sided continuity follow-up (2026-10-26)

Five mathematical proof rewrites pass the complete warning-free 1,799-module
build (10,507 Lake jobs), both public literal/axiom probes, all five public-module
kernel replays, and the script suite (115 passes, one optional fixture skip).
All 10,386 public declaration kinds/type hashes match the previous complete
main snapshot, with no missing or added public declarations. All 1,805 pinned
source/configuration/checker inputs match after every gate.

The freshly extracted local Blueprint retains 68 nodes, 120 edges and six
public exits. The rejected 165-module import experiment was fully restored;
only five approved continuity proof files differ from the baseline. See the
[report](LILIU_CONTINUITY_CLEANUP.md) and
[acceptance record](../research/liliu-continuity-cleanup/validation.json).
Separate concurrent Wu research changes are outside this main acceptance.

## Wu LiuPan lemma pruning (2026-10-27)

The nine-file, 383-lemma deletion passes the complete 4,142-module scope:
3,165 fresh isolated compilations and 977 verified unchanged dependencies.
Independent literal acceptance, five axiom reports and ten isolated kernel
replays pass. After exact artifact adoption, production `BUILD_PASS 4142`,
literal acceptance and the final `WR2ClassicalCertificate` replay also pass.
The retained text, numerical precision and exact 1.8938 endpoint are unchanged.
The first standalone replay encountered a 4.35 `Init` / 4.33 checker header
mismatch; its failure is retained. Fixing only the validator's `LEAN_SYSROOT`
to the pinned 4.33 toolchain enabled all ten replays.
See [the report](WU_LIUPAN_PRUNING.md) and
[actual acceptance records](../research/wu-liupan-pruning-audit/validation.json).

## Wu Fifth integer payments (2026-10-27)

The 4,142-module research source/receipt build, literal statements and standard
axioms, four generator checks, exact source-value/preservation audits and
9 named independent kernel replays pass. All 3,072 original payments,
48 separate 64-point sums and three totals are unchanged. The phase removes
3,779 effective lines, 3,699 physical lines and 39 modules.
See [the acceptance audit](../research/wu-fifth-integer-audit/validation.json).

## Wu light numeric layers (2026-10-27)

The then-current 4,181-module source build, literal/axiom probes, source
verification, three generator checks and 12 named independent kernel
replays pass. The phase removes 517 effective lines and 86 modules while
preserving all 104 independent payment proofs. See [the audit](../research/wu-light-layer-audit/validation.json).

## Wu Fourth Bq formula (2026-10-27)

The then-current **4,267-module** source build, literal/axiom probes, source
verification and named independent kernel replays pass. The original payments,
precision and final theorem are preserved. This phase removes 12,882
effective lines. See [the audit](../research/wu-fourth-bq-audit/README.md).

## Wu Eighth integer payments (2026-10-27)

The then-current **4,431-module** source build, literal/axiom probes, source
verification and named independent kernel replays pass. The original payments,
precision and final theorem are preserved. This phase removes 2,481
effective lines. See [the audit](../research/wu-eighth-integer-audit/README.md).

## Wu Sixth integer payments (2026-10-27)

The then-current **4,459-module** source build, literal/axiom probes, source
verification and named independent kernel replays pass. The original payments,
precision and final theorem are preserved. This phase removes 10,800
effective lines. See [the audit](../research/wu-sixth-integer-audit/README.md).

## Wu exact integer payments (2026-10-27)

The then-current **4,583-module** source build, literal/axiom probes, source
verification and named independent kernel replays pass. The original payments,
precision and final theorem are preserved. This phase removes 5,123
effective lines. See [the audit](../research/wu-integer-audit/README.md).

## Wu Hf4 shared certificates (2026-10-27)

The then-current **4,643-module** source build, both literal/axiom probes,
source verifier and six independent kernel replays pass. All 76,200 rational
fields and 80 retained panel statements match the accepted baseline. The
17-file generator check passes. This phase removes 5,404 effective lines.
See [that phase’s audit](../research/wu-shared-audit/README.md).
The following sections describe historical accepted snapshots.

## Wu derived-table and eighth-correction compression (2026-10-27)

The then-current **4,641-module** source build, both literal/axiom probes,
source verifier and independent kernel replays pass. Exact recurrences retain
all original values, precision and bounds while removing 20,210 effective
Lean lines. Both generators and 352 retained statement contracts pass.
See [that phase’s audit](../research/wu-derived-audit/README.md).
The following sections describe historical accepted snapshots.

## Wu cumulative-table and exact-certificate compression (2026-10-26)

The then-current **4,713-module** build, source/receipt checks and both literal/axiom
probes pass. Six independent kernel replays cover the seventh/ninth/sixth
soundness helpers, cumulative payment theorem, fourth concrete assembly and
final theorem over accepted imports. All 120 retained statement contracts and
21,082 reconstructed table values match the original; grids and precision are
unchanged. Four generator checks pass. See [that phase’s audit](../research/wu-table-audit/README.md).
The following sections record preceding accepted snapshots.

## Wu Hf4 exact-kernel compression (2026-10-26)

The then-current **4,774-module** source build and both literal/axiom checks pass.
The compact-kernel identity, integration bridge, rational model helper, first
complete panel and final theorem pass independent kernel replay over accepted
imports. All 40 original panel bound statements are preserved; the numerical
models are tighter at unchanged grid and rounding precision. The generator
reproduces all 15 generated modules exactly. See [the Hf4 audit](../research/wu-hf4-audit/README.md).
The following sections record earlier accepted snapshots.

## Wu structural simplification (2026-10-26)

The current full 4,771-module build and both literal/axiom checks pass. The two
modified source files preserve every mathematical statement and all numerical
tables. Independent kernel replay passes for `WSrcFifthGainAnalyticEnvelope`
and `WR2ClassicalCertificate`. See [the structural audit](../research/wu-structural-audit/README.md).
The isolated Hf4 candidate is checked separately and is not imported by the
accepted theorem. The next section records the preceding phase.

## Accepted Li–Liu cleanup, two waves (2026-10-26)

The current main snapshot passes the warning-free build of **1,799 modules
(10,507 Lake jobs)**, both literal/axiom probes and all five public-module
kernel replays. All pinned inputs and the exact main inventory match after each
gate. The script suite reports 115 passes and one optional full-export fixture
skip. Kind/type hashes match for all **10,385 surviving public declarations**;
1,481 intentional internal removals are listed explicitly. All six public
Chen/Li–Liu endpoint statements retain their original constants and quantifiers.

The new local Blueprint has 68 nodes, 120 edges and all six
expected public exits. The post-build scan records its remaining candidates,
without treating import-only or unreached declarations as automatically removable.
The separate Wu research tree has concurrent edits; its optional receipt/literal
check is not accepted in this phase. Main acceptance and that external check
are recorded separately, with the latest independent Wu acceptance linked.

See the [cleanup report](LILIU_CLEANUP.md),
[validation](../research/liliu-cleanup/validation.json),
[type comparison](../research/liliu-cleanup/type-preservation.json) and
[Blueprint evidence](../research/liliu-cleanup/blueprint-validation.json).
Older acceptance sections below retain their own historical source snapshots.

## Wu 1+1.8938 and second compression (2026-10-26)

The current **4,771-module** Wu inventory passes the full build and source,
object and dependency receipt checks. Independent literal probes check both
`one8938` (`r^5000 ≤ q^4469`) and the legacy `one894`. Their axiom reports
contain only `propext`, `Classical.choice` and `Quot.sound`. The two new rational
helpers, the stronger count conversion and the final module pass independent
kernel replay over the verified imports.

The new generator reproduces all 98 proof modules. All 13 tables touched across
both phases remain byte-identical, and this phase preserves 4,669 modules outside
its declared cohort. Compiled comparison retains 216,096 public
declaration types; the report lists changed internal finite-block types and
new endpoint declarations explicitly. See the [report](WU_18938_COMPRESSION.md)
and [validation](../research/wu18938-audit/validation.json). Older counts below
are historical phase snapshots. Main Chen/Li–Liu libraries are not rebuilt here.

## Precision-preserving Wu compression (2026-10-26)

The separate Wu inventory passes all **5,441** source/object/dependency checks,
the exact `one894` literal and standard-axiom probes, and independent replay of
the final module plus the four new rational soundness modules. The 11 numeric
tables and all 4,926 original non-generated modules are byte-identical to the
baseline. All three generators reproduce their 323, 55 and 133 outputs.

Compiled declaration comparison preserves 223,214 public types,
including 222,046 in non-generated modules.
The changed retained public types are 487 internal finite proof
blocks and 28 generated coverage auxiliaries whose compilation partition changed. Final mathematical interfaces and
all original numerical precision remain unchanged. See the
[report](WU_PRECISION_COMPRESSION.md) and [validation record](../research/wu-precision-audit/validation.json).
This phase does not rebuild the unchanged main Chen/Li–Liu libraries. The older
8,826-module Wu records below describe their original historical snapshots.

## Accepted original-paper follow-up

After comparing the five supplied original papers, the main tree passes the
warning-free build of **2,143 source modules (10,851 Lake jobs)**, both
literal-statement/axiom probes and the five public-module kernel replays listed
below. All 2,149 pinned source/configuration/checker inputs and the exact source
inventory match after every gate. The public targets retain their quantitative
constants, including Chen's `0.67` lower bound.

The structural type census compares **11,864 surviving public declarations**
from the complete previously accepted main library, with no missing declarations
or type-hash differences after excluding private and specified generated names.
Two previously private generic inversion helpers are made public for the
specializations. The original public definitions are retained.

The script suite again records 115 passes and one skipped optional full-export
corruption fixture, out of 116 tests. Wu's unchanged 8,826-source manifest,
history hashes, literal statement, axioms and source-bound receipts pass again;
the historical full Wu rebuild and final replay are not repeated in this phase.

The local Blueprint is extracted and rendered from the accepted working tree:
68 selected nodes, 125 compiled dependency edges, four chapter graphs and
all six expected theorem exits. Updated catalogue source positions are checked
against the freshly extracted artifacts. This is a local render, not a
publication or deployment record.

The [validation record](../research/chen-paper-audit/validation.json),
[pinned inputs](../research/chen-paper-audit/validation-inputs.json),
[type comparison](../research/chen-paper-audit/type-preservation.json),
[dependency census](../research/chen-paper-audit/analysis-after-fulltext.json) and
[Blueprint validation](../research/chen-paper-audit/blueprint-validation.json)
identify this snapshot. The [paper comparison](CHEN_PAPER_COMPARISON.md) records
source pages and implementation decisions; the [size report](SOURCE_SIZE.md)
separates the additional 598-line reduction from the earlier structural cleanup.
Raw logs, OCR and compiled objects remain local and untracked; a fresh checkout
must regenerate its build evidence. The previous cleanup acceptance below is
retained as a historical snapshot.

## Historical accepted Chen cleanup (2026-10-25)

The cleanup against `c4e1b8d0` passes the full warning-free build of all
**2,142 main source modules (10,850 Lake jobs)**, both literal-statement and
axiom probes, and independent replays of `Goldbach.Theorem`, `Goldbach.Checks`,
`Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`.
The queue pins 2,148 source/configuration/checker inputs and verifies their
hashes and exact source inventory after every gate. Retired objects for deleted
modules were removed from the active import path before rebuilding.

The local Blueprint is also re-extracted, rendered and verified: 68 nodes,
125 edges, four chapter graphs and all six expected theorem exits. Its
67 refreshed source locations are recorded in the
[Blueprint validation](../research/chen-audit/blueprint-validation.json).

All 116 script tests are accounted for: 115 pass; one full-export corruption
test is skipped because its optional export fixture was not supplied.
A separate structural type census compares
5,302 surviving public declarations from the original Chen closure, with no
type-hash differences. The endpoint probes independently preserve the exact
public targets and limit reported axioms to `propext`, `Classical.choice` and
`Quot.sound`.

The unchanged Wu tree passes its source/history hash verification and its
literal/axiom gate with source-bound receipts for all 8,826 modules. This cleanup
does not rerun the historical full Wu build or final Wu kernel replay. Those
accepted records remain dated 2026-10-24 below.

The [validation record](../research/chen-audit/validation.json),
[pinned input hashes](../research/chen-audit/validation-inputs.json),
[type comparison](../research/chen-audit/type-preservation.json), and
[post-cleanup dependency census](../research/chen-audit/analysis-after-cleanup.json)
identify this working-tree snapshot. Raw logs and objects remain local and
untracked. New checkouts must regenerate their own build evidence. The
[cleanup audit](CHEN_REDUNDANCY_AUDIT.md) describes the removed internal modules;
the [size report](SOURCE_SIZE.md) counts actual source reductions.

## Historical accepted source snapshot (2026-10-24)

The main acceptance run built all 2,533 shipped source modules (11,241 Lake jobs),
passed both literal/axiom probes and replayed `Goldbach.Theorem`,
`Goldbach.Checks`, `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks`
and `Goldbach.All`. All 2,537 pinned source/configuration/checker inputs matched
the accepted snapshot at final review. The separate Wu run built all 8,826
manifest modules and passed its literal/axiom gate and final-module replay.

The tracked [completion record](../research/wu2008/completion-audit.json) and
[research status](../research/wu2008/mathematical-status.json) retain the results
and fingerprints. Raw build logs, receipts and compiled objects live in ignored
local build directories; a fresh checkout must run the commands above and the
research README's commands to generate its own evidence. The [source-size
report](SOURCE_SIZE.md) distinguishes full build inventories from each endpoint's
local import closure.

## Li–Liu endpoint inspection

After building `Goldbach.OnePlusOneNine`, the following commands in a Lean file
inspect all four public declarations and their transitive axiom dependencies:

```lean
import Goldbach.OnePlusOneNine

#check Goldbach.one_plus_one_nine
#check Goldbach.one_plus_one_nine_real
#check Goldbach.one_plus_one_nine_count
#check Goldbach.one_plus_one_nine_lower_bound
#print axioms Goldbach.one_plus_one_nine
#print axioms Goldbach.one_plus_one_nine_real
#print axioms Goldbach.one_plus_one_nine_count
#print axioms Goldbach.one_plus_one_nine_lower_bound
```

Run the file with `lake env lean path/to/check.lean`. Compare the displayed types
with [THEOREMS.md](THEOREMS.md): retain `r^10 ≤ q^9`, the count of distinct actual
primes `p`, the strict coefficient `1/2500`, and the choice of
`κ < 515093/800000000` before the threshold. The allowed logical axioms are
`propext`, `Classical.choice` and `Quot.sound`.

A separate module replay is available with:

```sh
lake env leanchecker --verbose Goldbach.OnePlusOneNine
```

This replays the new facade over its cached imports. To replay all four project
libraries after a full build, use:

```sh
lake env leanchecker --verbose Goldbach MathlibNt AnalyticNumberTheory PrimeNumberTheoremAnd
```

The pinned checker expands these module-name prefixes; the pinned Mathlib
artifacts supply the external dependency environment. Historical Chen comparator
and replay records retain their original 1+2 scope.

## Acceptance gates

1. **Source build:** `lake --wfail build` builds all four default libraries,
   covering all shipped project-proof modules, both public interfaces and the acceptance
   checks. Lean elaborates the source and its kernel checks the resulting proof
   terms as modules are compiled.
2. **Source surface:** `python3 scripts/check.py --static-only` scans all shipped
   Lean files for missing local imports, import cycles and source reachability.
   It flags the tokens `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` and
   `debug.skipKernelTC` after masking nested comments and string literals.
   These rules catch proof placeholders, custom axiom declarations, trusted
   native decision calls, unsafe declarations and the kernel-check bypass option
   at the source level. The release-text scan also checks for untranslated CJK
   content and private machine paths, including Blueprint source and renderer
   configuration. `Goldbach.Blueprint` is a separate documentation root in the
   reachability check, alongside the public and check roots.
3. **Literal targets and axiom dependencies:** `python3 scripts/check.py` runs
   the source checks and elaborates two separate probes. `Goldbach/Checks.lean`
   expands the Chen specification, verifies its implementation signatures,
   quantitative coefficient, normalization and actual representation count, and
   checks repeated prime factors and the second summand's lower bound. Its four
   axiom reports cover the two Chen public results and their implementation
   endpoints. `Goldbach/OnePlusOneNineChecks.lean` checks the four Li–Liu public
   results and reports their axioms. Every expected report must appear exactly
   once, and every reported axiom must belong to the allowed set
   `propext`, `Classical.choice`, `Quot.sound`.
4. **Independent module replay:** `lake env leanchecker --verbose Goldbach.Theorem`
   uses the matching Lean checker in a separate process to replay compiled
   declarations in `Goldbach.Theorem` over its cached imports. The imports supply
   the dependency environment for this module-level replay; the full source
   build above checks the project's source closure. Run the replay in an
   environment with `LEAN_PATH` and `LEAN_SRC_PATH` clear of values inherited
   from another project. CI also replays `Goldbach.Checks`,
   `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`
   as separate modules over their cached imports.
5. **Isolated reconstruction:** extract the source archive into an independent
   directory, fetch the pinned dependencies, and run the same commands. Build
   project `.olean` files from the extracted sources in that directory; obtain
   dependency artifacts through the pinned dependency setup.

The logical foundation is Lean's standard propositional extensionality
(`propext`), classical choice (`Classical.choice`) and quotient soundness
(`Quot.sound`). The axiom gate accepts any subset of these three and rejects
additional axioms, missing reports and duplicate reports. `check.py` clears
inherited `LEAN_PATH` and `LEAN_SRC_PATH` before invoking Lean.

## How the checks fit together

The lexical scanner checks source tokens and import structure. It handles nested
comments and strings; Lean's parser, elaborator and kernel handle Lean syntax,
types and proof terms. The axiom reports identify the transitive logical
assumptions used by each endpoint. The literal target checks establish the types
of the public results, and the proved almost-prime conversion connects the
internal representation predicate to primes and products of two primes.
Together these checks cover the implementation, its logical dependencies and
its public mathematical statement.

The existence theorems quantify over every even natural number above an
existential threshold. Their universal scope comes from the Lean proofs. The threshold and
quantifier order are given in [THEOREMS.md](THEOREMS.md).

The release build uses `lake --wfail build`: every reported warning fails the
build, including warnings replayed from cached modules. The public statement
check also enables `warningAsError`. Resolve each warning at its source and
keep the warning gate active alongside the theorem-type and axiom checks.

## Source size and website checks

`python3 scripts/check.py --static-only --count-lines` additionally reports
nonblank Lean source lines with nested comments removed and string literals
retained. Release notes use this convention to measure source size.

The documentation pipeline checks generated module coverage, declaration search
anchors, local links and site routes. Its source-only regression tests include
API-only and legacy-bundle assembly inputs and deployment-boundary checks.
See [DOCUMENTATION.md](DOCUMENTATION.md) for the commands and browser checks.
