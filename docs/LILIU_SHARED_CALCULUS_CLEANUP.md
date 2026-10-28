# Li–Liu: shared calculus and author-weight proofs

This phase starts from the [accepted quartic-log snapshot](LILIU_QUARTIC_LOG_CLEANUP.md):
201,849 main effective lines, a 194,294-line Li–Liu closure and a 99,269-line Chen
closure. Nine existing main-library files change. No module, import or auxiliary
Lean probe is added. All 10,406 old public names/kinds/type hashes remain.
Two existing private G11 proofs become shared public helpers.

## Shared analytic proofs

The original G11 `g11_log_ratio_deriv` becomes public
`goldbach_log_ratio_deriv`, with its statement and proof unchanged. G12 deletes
its duplicate private proof and invokes that helper. Its existing direct import
of G11PrimeKernelReduction already supplies the theorem. The full statement still
assumes `b > 0` and `x > 0` and differentiates `log(b/y)` to `-1/x` at `x`.
Both original G11 consumers and the G12 primitive-derivative consumer actually
reach the shared proof. The statement is not restricted to a mesh or interval.

The original G11 `g11_integral_four` similarly becomes public
`goldbach_integral_four`. G12CrossMesh already imports its G11 integration provider
through G11PrimeKernelMeshLimit, so its duplicate proof can be deleted without
any import changes. The full joint `Integrable F` hypothesis on
`(Real×Real)×(Real×Real)` remains. The original almost-everywhere Fubini argument is
unchanged; separate integrability at every parameter value is not assumed.
Both original public mesh-integral identities actually reach the common proof.
The source regions, kernels, density definitions and mesh data are unchanged.

Four private names disappear: two existing G11 proofs are promoted and two G12
copies are deleted. Each old kind/type hash matches its shared public replacement.
G11 log differentiation originally had two incoming declarations; each other
helper had one. All five original consumers remain and actually reference the
appropriate shared proof. No outside-provider consumer of an old private name
is lost. This does not claim four independently redundant complete proofs.

## Complex powers and author weight

Both Mellin-continuation files retain their private `mul_error_cpow` names and
complete statements. Their manual calculation is replaced by a direct use of
`Complex.cpow_add`, followed by additive simplification. For real `t > 0` and
arbitrary complex `s`, the statement remains
`(t:Complex)*(t:Complex)^(-(s+1)) = (t:Complex)^(-s)`.
The positive real base still proves the required nonzero complex base. No
complex-product or branch-cut identity is assumed, and all convolution/Mellin
continuation hypotheses remain unchanged. Both compiled proofs actually reach
Mathlib's original `Complex.cpow_add` theorem.

The existing public `goldbachG11AuthorWeight_global_upper` statement and complete
proof move from AuthorFinalScalar to the actual G11PrimeKernel definition
provider. G12AuthorWeightBounds already imports that provider directly and keeps
its original public `goldbachG12AuthorWeight_le_eight` name/type as a one-line call.
The cap remains global for every real argument, with no interval, positivity or
evenness hypothesis. The formula `36/(5*(1-min r (1/10)))` is unchanged.
The original public name/proof is retained rather than importing the later G11
final application into the G12 leaf module. No reverse dependency is introduced.

## Measurements

| Source group | Net effective-line change |
|---|---:|
| Shared log-ratio derivative | -8 |
| Shared four-variable Fubini identity | -9 |
| Two direct complex-power proofs | -6 |
| Shared existing author-weight cap | -4 |
| Complete phase | -27 |

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,803 | 1,803 | 0 |
| Main effective lines | 201,849 | 201,822 | -27 |
| Li–Liu closure modules | 1,432 | 1,432 | 0 |
| Li–Liu closure effective lines | 194,294 | 194,267 | -27 |
| Chen closure effective lines | 99,269 | 99,263 | -6 |

All promoted proof bodies, public aliases and the moved five-line global weight
proof are counted. All nine import lists are identical. Main physical lines
change by -26; UTF-8 bytes by -1,058.
Only the two complex-continuation files belong to Chen's import closure; their
three-line savings each account for its six-line reduction. Shared dependencies
count independently in each theorem closure. External Lake dependencies are
excluded. No proof moves outside the measured main tree. The existing 17-line
internal-statement probe is reused unchanged; no auxiliary Lean code is added.
No minimality or build-speed claim is made.

## Acceptance

All nine gates pass: warning-free 1,803-module full source build (10,511 Lake jobs),
both public literal/axiom checks, unchanged internal-strengthening contracts,
five named-module kernel replays and script tests (115 passes and one optional
full-export fixture skip). Replays cover `Goldbach.Theorem`, `Goldbach.Checks`,
`Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`
over rebuilt imports; independent replay of every imported module is not claimed.
All 1,809 main source/configuration/checker pins and the separately pinned
statement probe match after each gate. The source inventory is unchanged.

The complete census preserves all 10,406 old public names/kinds/type hashes,
with no missing public declarations. Only the two promoted analytic helper names
are added, bringing the public count to 10,408. All four old private analytic
statements match their replacements' kinds/type hashes. Both private complex
statements keep their names/types. The existing public weight-cap name retains
its type at its new provider. Actual compiled references verify the intended
shared proofs and every original consumer recorded above.

All nine complete-file prototypes passed warning-as-error compilation before
application, with matching source/log fingerprints rechecked. Four consumer
prototypes contain the actual promoted/moved proofs rather than forward
assumptions; provider prototypes contain the complete new files. The complex
simplification also passed an isolated Mathlib-only proof before the two complete
Mellin files were compiled. Complete production-combination acceptance is separate
from these historical prototype receipts.

All six public endpoints retain their exact constants and quantifier order:
`D19`, prime conditions, `r^10 ≤ q^9`, the genuine real exponent, Liu's singular
series, strict `1/2500`, fixed `κ < 515093/800000000` before the threshold and
Chen's `0.67`. Public axioms remain only `propext`, `Classical.choice` and
`Quot.sound`. The final producer guard, original numerical grids, precision,
error constants and release checks are unchanged. Fresh Blueprint extraction,
local rendering, source positions, graph, annotations and tests pass:
68 nodes, 120 edges, four chapters and all six original exits.

This is an uncommitted local snapshot. Separate concurrent `research/wu2008`
sources, certificates and documentation are outside this phase. Historical
source-size cohorts remain separate from current totals.

See [validation](../research/liliu-shared-calculus-cleanup/validation.json),
[pinned inputs](../research/liliu-shared-calculus-cleanup/validation-inputs.json),
[type preservation](../research/liliu-shared-calculus-cleanup/type-preservation.json),
[nine-file changes](../research/liliu-shared-calculus-cleanup/changes.json),
[exact private replacements](../research/liliu-shared-calculus-cleanup/private-proof-redirects.json),
[retained complex statements](../research/liliu-shared-calculus-cleanup/retained-private-statements.json),
[moved public weight cap](../research/liliu-shared-calculus-cleanup/moved-public-proofs.json),
[actual shared-proof references](../research/liliu-shared-calculus-cleanup/shared-proof-references.json),
[closure membership](../research/liliu-shared-calculus-cleanup/scope-membership.json),
[source sizes](../research/liliu-shared-calculus-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-shared-calculus-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-shared-calculus-cleanup/reproduce.py --output /tmp/liliu-shared-calculus-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` requests separate checks of a stable rebuilt Wu tree.
Unimplemented follow-up candidates are excluded from the savings above.
