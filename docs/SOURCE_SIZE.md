# Source size and proof simplification

The current measurements compare the working tree against accepted commit
`c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`. The
[current machine-readable report](../research/liliu-finite-prefix-cleanup/source-size.json)
counts the complete main source tree, including moved code, additions and
deletions. Reproduce the main report with `python3 research/liliu-cleanup/measure_main.py`.

The main rows describe this accepted Chen/Li–Liu snapshot. The Wu row is the
latest independently accepted [structural compression snapshot](../research/wu-structural-compression-audit/measurement.json).
Wu research acceptance is separate from the main acceptance. The main
measurement tool does not read that changing research tree; the combined
`scripts/source_size.py` additionally requires a matching Wu source manifest.

## Size of each theorem's local import closure

| Result | Modules before → current | Effective code lines before → current | Physical lines current |
|---|---:|---:|---:|
| Chen 1+2: `Goldbach.Theorem` | 743 → 528 | 216,923 → 99,214 | 119,981 |
| Li–Liu 1+1.9: `Goldbach.OnePlusOneNine` | 1,733 → 1,432 | 331,316 → 194,201 | 230,788 |
| Wu04/Wu08 1+1.8938 (also 1+1.894): `WR2ClassicalCertificate` | 8,444 → 3,764 | 1,126,636 → 525,529 | 621,451 |

Each row counts the entry module and every transitively imported local module
once within that row. Shared dependencies occur in multiple rows, so the rows
must not be added. External Lake dependencies, including Mathlib, are excluded;
the adapted local `PrimeNumberTheoremAnd` sources are included. The Wu row uses
the separate research tree and includes generated numerical certificates. Its
accepted full inventory contains 4,151 modules and 566,283 effective lines. The
[latest Wu audit](WU_STRUCTURAL_COMPRESSION.md) records 7,612 fewer effective Lean
lines and 9,092 fewer physical lines in both scopes; the cumulative closure
saving is 601,107 effective lines. Original grids, precision and numerical bounds
are preserved. The preceding [383-lemma phase](WU_LIUPAN_PRUNING.md) and earlier
compression measurements remain historical snapshots in their audit directories.

Effective code lines are nonblank lines after removing Lean line comments and
nested block comments, retaining string literals and code before inline comments.
Physical lines also include comments and blank lines. Both metrics count whole
modules, including definitions, statements, commands and proofs. They do not
measure a smallest declaration-level proof.

## Cumulative whole-tree reduction

| Metric | Before | Current | Change |
|---|---:|---:|---:|
| Main Lean modules | 2,533 | 1,803 | -730 |
| Effective code lines | 350,143 | 201,756 | -148,387 (-42.38%) |
| Physical lines | 411,423 | 240,429 | -170,994 |
| UTF-8 bytes | 20,652,937 | 12,220,603 | -8,432,334 |

The current tree deletes 739 baseline modules, adds 9 common modules and
modifies 941 existing modules. Moved code is included in every current total.

## Contribution of each simplification phase

| Phase | Main effective lines before → after | Net main saving | Chen import-closure saving |
|---|---:|---:|---:|
| First structural cleanup | 350,143 → 234,557 | 115,586 | 117,136 |
| Five-original-paper comparison | 234,557 → 233,959 | 598 | 598 |
| Li–Liu cleanup wave 1 | 233,959 → 204,151 | 29,808 | 1 |
| Li–Liu cleanup wave 2 | 204,151 → 203,062 | 1,089 | -38 |
| One-sided continuity follow-up | 203,062 → 203,002 | 60 | 0 |
| Shared log/harmonic foundations | 203,002 → 202,991 | 11 | -22 |
| Finite weighted-cell calculus | 202,991 → 202,902 | 89 | -4 |
| Shared continuity and scalar bounds | 202,902 → 202,818 | 84 | 17 |
| Uniform local products and error payments | 202,818 → 202,626 | 192 | 11 |
| Carrier identities, growth and finite fibers | 202,626 → 202,472 | 154 | -22 |
| Endpoint positivity, scales and labelled atoms | 202,472 → 202,394 | 78 | 0 |
| Shared low-conductor budgets and Pan maxima | 202,394 → 202,207 | 187 | -14 |
| Shared finite coprimality-gate budgets | 202,207 → 202,026 | 181 | 0 |
| Finite-sum, log-payment and grid helpers | 202,026 → 201,992 | 34 | 7 |
| Shared boundary-integral and low-positivity proofs | 201,992 → 201,865 | 127 | 0 |
| Shared quartic-log remainder payment | 201,865 → 201,849 | 16 | -16 |
| Shared calculus and author-weight proofs | 201,849 → 201,822 | 27 | 6 |
| Shared finite-prefix and squarefree-divisor proofs | 201,822 → 201,756 | 66 | 49 |

The first phase removes unused historical branches and declarations, consolidates
analytic providers, narrows the PNT route and derives existence from the `0.67`
count. Its [audit](CHEN_REDUNDANCY_AUDIT.md),
[measurements](../research/chen-audit/source-size-after-cleanup.json) and
validation records remain a historical accepted snapshot.

The [full-text follow-up](CHEN_PAPER_COMPARISON.md) consolidates three finite
Selberg optimizer proofs into one general truncated theorem and its two
specializations. The 598-line net saving includes the extracted module. Both
the Chen and Li–Liu closures save 598 lines. The necessary divisor-sum bound
is now imported explicitly by its varying-prime consumer; its finite-weight
proof remains separate from the generic optimizer.
The [incremental file record](../research/chen-paper-audit/changes.json)
separates this phase from the earlier savings.

The [implemented Li–Liu cleanup](LILIU_CLEANUP.md) saves **30,897 main lines**
across two waves. Its Li–Liu import closure falls from 219,749 to 196,547 lines:
**23,202 fewer lines (10.56%)**. The second wave's shared generic factors and
continuity theorem add 38 lines to Chen's closure compared with wave 1; including
the first wave's one-line import removal, Chen grows by 37 lines relative to the
paper-follow-up snapshot. Shared code and all extractions are included.
Concurrent Wu reductions are separate and do not contribute to these main totals.

The [continuity follow-up](LILIU_CONTINUITY_CLEANUP.md) removes another 60 lines
from both main sources and the Li–Liu closure, without module deletions.
The [shared-foundation follow-up](LILIU_LOG_KERNEL_CLEANUP.md) then saves
11 main lines and 1,086 Li–Liu closure lines, including both new modules
and all moved code. Chen's closure grows by 22 lines through shared dependencies.
The [finite-cell calculus follow-up](LILIU_GRID_CALCULUS_CLEANUP.md) then saves
another 89 main lines and 54 Li–Liu closure lines, including the three
generic lemmas. Chen's closure grows by another 4 lines through the shared module.
The [shared-lemma follow-up](LILIU_SHARED_LEMMA_CLEANUP.md) saves another
84 production main lines, 84 Li–Liu closure lines and 17 Chen closure lines.
Its additional research acceptance probe contains 17 effective Lean lines, so the
phase saves 67 lines when that new probe is also counted.
The [local-product follow-up](LILIU_PRODUCT_CLEANUP.md) saves another
192 main lines and 192 Li–Liu closure lines, including the new 37-line shared module.
Chen's closure saves another 11 lines. It reuses the existing statement probe without
adding auxiliary Lean code.
The [carrier/growth follow-up](LILIU_CARRIER_CLEANUP.md) saves another
154 main lines and 154 Li–Liu closure lines, counting all moved proof bodies and imports.
Chen's closure grows by +22 lines through the existing shared log-power foundation.
It adds no production module or auxiliary Lean probe.
The [endpoint follow-up](LILIU_ENDPOINT_CLEANUP.md) saves another
78 main lines and 78 Li–Liu closure lines, counting all shared proof bodies and callers.
It adds no module or auxiliary Lean probe; Chen's closure is unchanged.
The [low-conductor/Pan follow-up](LILIU_LOW_BUDGET_CLEANUP.md) saves another
187 main and 187 Li–Liu closure lines, including the new shared maximum theorem and direct import.
Chen's closure grows by +14 lines through its shared providers. It adds no
production module or auxiliary Lean probe.
The [finite coprimality-gate follow-up](LILIU_GATE_BUDGET_CLEANUP.md) saves another
181 main and 181 Li–Liu closure lines, including all 116 lines in its new shared
provider. Chen's complete closure totals remain unchanged. It adds one production
module and no auxiliary Lean code.
The [finite-helper follow-up](LILIU_FINITE_HELPER_CLEANUP.md) saves another
34 main and 34 Li–Liu closure lines, counting all moved code and direct imports.
Chen's closure saves 7 lines through its quadratic explicit Pólya–Vinogradov
provider. No module or auxiliary Lean code is added.
The [boundary-integral follow-up](LILIU_BOUNDARY_INTEGRAL_CLEANUP.md) saves another
127 main and 127 Li–Liu closure lines, including both direct imports and all moved
positivity code. Chen's complete closure totals are unchanged. No module or
auxiliary Lean code is added.
The [quartic-log follow-up](LILIU_QUARTIC_LOG_CLEANUP.md) saves another 16 main
and 16 Li–Liu closure lines, including all 16 added shared-provider lines. Chen's
source closure grows by 16 lines because it imports that provider; neither Chen
public theorem's compiled reference cone reaches the new helper. No module or
auxiliary Lean code is added.
The [shared-calculus follow-up](LILIU_SHARED_CALCULUS_CLEANUP.md) saves another
27 main and 27 Li–Liu closure lines, counting both promoted analytic proofs and
all moved weight-cap code. Chen's closure saves 6 lines through the two Mellin
continuation files. No module, import or auxiliary Lean code is added.
The [finite-prefix follow-up](LILIU_FINITE_PREFIX_CLEANUP.md) saves another 66 main
and Li–Liu closure lines, counting every canonical proof and WF wrapper. Chen's
closure saves 49 lines through the two existing finite-sieve providers. No module,
import or auxiliary Lean proof is added.
Current totals are 201,756 main and 194,201 Li–Liu closure lines.
The rejected import experiment is excluded from every saving above.

No comparable before/after build-time benchmark was recorded. The
[historical benchmark](BUILD_BENCHMARK.md) concerns other release revisions;
source reduction alone does not establish a build-time improvement.

## Historical refactoring accepted on 2026-10-24

The baseline is commit `09b97db5764ade1246bfb77206baa1b124760958`. The refactoring
cohort consists of the 25 modified tracked main-library modules plus all three
split-out representation/data modules. Moved code is included in the new total.

| Metric | Before | After | Change |
|---|---:|---:|---:|
| Effective code lines | 7,704 | 7,575 | -129 (-1.67%) |
| Physical lines | 8,999 | 8,908 | -91 |
| UTF-8 bytes | 609,046 | 600,085 | -8,961 |

The changes share finite-fibre counting lemmas, simplify the Chen weight proof,
separate finite representation and rational polynomial data from analytic proofs,
and remove unused hypotheses from Buchstab core estimates while keeping old
interfaces as specializations. The principal benefit is a clearer proof structure.

The complete main tree also gains 16 other proof modules. Counting every addition,
the main tree grows from 349,039 to 350,143 effective lines: **+1,104 lines**,
with +1,461 physical lines and +59,493 bytes. That snapshot contains 2,533 modules.
These whole-tree figures must not be presented as a net reduction.

No comparable before/after build-time benchmark was recorded for this work.
The [historical benchmark](BUILD_BENCHMARK.md) concerns different Chen release
revisions. The [verification guide](VERIFICATION.md) records the current build
and acceptance scope.
