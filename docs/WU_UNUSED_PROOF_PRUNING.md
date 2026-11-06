# Wu unused-proof pruning

This phase is installed and accepted. The final `WuPaper.ClassicalSlots.one8938`
theorem and legacy `one894` interface remain. The exact power inequality is still
`r ^ 5000 ≤ q ^ 4469`. Numerical definitions, grids, precision and error budgets
are unchanged.

| Scope | Modules | Effective lines before → current | Physical lines before → current |
|---|---:|---:|---:|
| Complete Wu source tree | 4,151 | 540,985 → 509,776 | 629,373 → 595,256 |
| Final theorem local import closure | 3,764 | 500,231 → 469,022 | 582,895 → 548,778 |

Both scopes save **31,209 effective lines, 34,117 physical lines and 1,829,704 bytes**.
Cumulative closure savings against the original 1,126,636 lines are 657,614 lines.
This phase does not recount the separate 25,298 lines saved by
[constructive Hf4 compression](WU_HF4_CONSTRUCTIVE.md).
The published `scripts/check.py` counter retains strings and counts complete
local modules, excluding external Lake dependencies. This is not a minimum
size of the declaration-level proof.

## Deletion evidence

The change removes 2,119 proof declarations from 1,082 modules: 2,097 public
declarations and 22 private lemmas. An actual private-inclusive census of the
old compiled environment covers all 4,151 modules and examines both declaration
types and proof bodies. Every target has zero direct incoming references.
Current sources, generators, documentation consumers and retained interfaces
are protected. Only explicitly archived work copies are excluded; their paths,
hashes and reasons remain in the historical evidence.

Deletion ranges come from actual compiler metadata. They include 1,326 attached
documentation comments and nine directives scoped solely to the deleted proof.
Every other character is identical before and after; no global attribute,
namespace command or data definition was deleted. The
[retired declaration index](../research/wu-unused-proof-audit/retired-declarations.json)
contains original runtime names, owners, exact fragments, compiler ranges and hashes.

Some original development comments still mention retired internal lemmas. These
are non-executable comments; they have not all been rewritten. The
[comment review](../research/wu-unused-proof-audit/comment-reference-review.json)
records 42 lines mentioning 29 retired names and one ordinary-word collision.
The original declarations remain traceable through the retirement index.
Two exact deletion results retain blank lines at EOF; default `git diff --check`
reports these two cosmetic warnings. Other whitespace checks pass with
`git -c core.whitespace=-blank-at-eof diff --check`. Accepted source hashes are
preserved rather than changing the compiled snapshot for this formatting issue.

## Verification scope

Incremental compilation follows the reverse import closure: 3,957 modules are
compiled, including 1,082 source changes and 2,875 downstream dependency rebuilds.
The remaining 194 recursively verified contexts reuse accepted cache artifacts.
All actual source compilations exit with code zero; original commands, logs,
source hashes, object hashes and dependency contexts are retained.

All 30 candidate gates pass. Raw exports of 696 retained types and 183 definition
values are identical. Exact new and legacy literal statements and standard
classical axiom checks pass. Twenty-one root-module kernel replays pass. Their
import closures cover the local inventory, but these commands omit `--fresh`
and therefore do not replay every imported declaration. Both the Hf4 and
C/eighth generators reproduce their outputs.
An old-library positive control must report a surviving retired name; the new
library confirms all 2,119 original full names are absent, including private names.
The expected old-control exit code one is separate from proof compilation failures.

Installation uses the accepted sources and objects, preserving original proof
receipts. Five actual post-install checks pass: both generators, recursive cache
receipts for all 4,151 modules, literal statements and axioms, and a final
root-module kernel replay (without `--fresh`). The post-install cache build executes no new source compilation;
installation is not reported as another compilation.

## Reproduction

- [Installed measurements](../research/wu-unused-proof-audit/measurement.json)
- [Current acceptance](../research/wu-unused-proof-audit/validation.json)
- [Actual isolated gates](../research/wu-unused-proof-audit/isolated/report.json)
- [Post-install checks](../research/wu-unused-proof-audit/production-verification.json)

Run from the repository root:

```sh
python3 research/wu-unused-proof-audit/measure.py
python3 research/wu-unused-proof-audit/verify.py
```

The second command checks compressed historical evidence, actual logs and current
source measurements; it does not rerun Lean. Absolute paths in historical commands
record the original environment and need not exist on another machine. Compiled
binary backups remain in the local ignored build directory; the compressed archive
contains text sources, receipts, commands and baseline consumers. The complete
proof can be rebuilt using the instructions in `research/wu2008/README.md`.

No comparable before/after build-time benchmark was recorded. This phase reports
actual source reduction without claiming a compilation speed improvement.
