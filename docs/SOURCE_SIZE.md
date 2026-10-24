# Source size and current refactoring

These measurements describe the accepted source tree on 2026-10-24. The
[machine-readable report](../research/wu2008/source-size-report.json) records
the exact baseline and per-file changes. Reproduce the measurements with
`python3 scripts/source_size.py`; its JSON output includes the measurement date.

## Size of each theorem's local import closure

| Result and entry module | Local modules | Effective code lines | Physical lines |
|---|---:|---:|---:|
| Chen 1+2: `Goldbach.Theorem` | 743 | 216,923 | 257,739 |
| Li–Liu 1+1.9: `Goldbach.OnePlusOneNine` | 1,733 | 331,316 | 389,113 |
| Wu04/Wu08 1+1.894: `WR2ClassicalCertificate` | 8,444 | 1,126,636 | 1,257,657 |

Each row includes the entry module and every transitively imported local module,
counted once within that row. Shared modules occur in multiple rows, so the rows
must not be added. External Lake dependencies, including Mathlib, are excluded;
the adapted local `PrimeNumberTheoremAnd` sources are included. The Wu row uses
the separate research source tree and includes generated numerical certificates.
The full research build covers 8,826 modules, including modules outside the final
theorem's import closure.

Effective code lines are nonblank lines after removing Lean line comments and
nested block comments, retaining string literals and code before inline comments.
Physical lines also include comments and blank lines. Both metrics count whole
modules, including definitions, statements, commands and proofs; neither measures
the smallest declaration-level proof of the result.

## What the recent simplification saved

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
with +1,461 physical lines and +59,493 bytes. It now contains 2,533 modules.
These whole-tree figures must not be presented as a net reduction.

No comparable before/after build-time benchmark was recorded for this work.
The [historical benchmark](BUILD_BENCHMARK.md) concerns different Chen release
revisions. The [verification guide](VERIFICATION.md) records the current build
and acceptance scope.
