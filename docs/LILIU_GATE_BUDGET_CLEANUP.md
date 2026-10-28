# Li–Liu: shared finite coprimality-gate budgets

This phase starts from the [accepted low-conductor/Pan snapshot](LILIU_LOW_BUDGET_CLEANUP.md):
202,207 main effective lines and a 194,652-line Li–Liu closure. Two existing
consumers change and one common main-library module is added. All 10,405 original
public names, declaration kinds and type hashes remain; no public name is added.

## Proof change

`FiniteCoprimeGateBudget` now owns the four existing `G11FiniteGate` theorems:
`inv_totient_prime_le`, `bad_inverseTotientMass_le`, `weightMass_le` and
`sum_gate_le_logCube`. Their complete namespace block is copied byte for byte
from G11GateBudget. The historical public names are preserved for callers.
G11GateBudget imports that provider and keeps its application-specific theorem.
The common module imports DirectConductorWeight, without a Goldbach carrier or
the G11 linked-window application. This keeps the main dependency graph acyclic.

B10's public `sum_gateLoss_le_logCube` specializes the shared weighted-support
gate at `K = 2`. For each actual support element `m = r*s`, the new local argument
uses `m.primeFactors = {r,s}`. Thus its distinct-prime-factor cardinality is at
most two, and the original carrier inequalities give `b ≤ r` and `b ≤ s`.
The existing support-interval proof supplies `S ⊆ Icc 1 N`. The shared theorem
then yields exactly `(4*T/b)*(1+log N)^3`, with the original hypotheses
`Q ≤ N`, `2 ≤ N`, `0 < b`, `0 ≤ T` and `|w m| ≤ T/m`.
The coefficient weights remain signed and the actual finite product support is
unchanged. No extra large-N, coprimality, squarefree or positivity assumption on
`w` is introduced. The distinct-factor set argument itself also covers repeated
prime factors. An empty support is handled by the common finite-sum theorem.

The exact `gateLoss` definition is source-identical. Its reciprocal-totient
factor, filtered non-coprime support, absolute value and modulus interval are
preserved; division versus multiplication is reconciled algebraically at the
call. The B10 public theorem and G11's arbitrary `K` theorem retain their complete
original types. Generic bounds for composite cofactors are not narrowed to two
primes.

Five old B10 private proof stages disappear: two reciprocal-totient bounds, the
specialized inverse-mass union bound, its weight-mass argument and its separate
harmonic-cube comparison. Each has exactly one old incoming declaration, inside
the same provider. Only the bound with arbitrary positive lower cutoff is claimed
to have an exact shared replacement kind/type hash. The remaining stages are
replaced as part of the full public specialization, not claimed as literal
type-equal aliases. Both private support bounds retain their types. Compiled
references verify that the B10 public proof reaches the shared gate, which still
reaches its actual inverse-mass and weight-mass proofs.

## Measurements

| Source | Effective lines before → after | Change |
|---|---:|---:|
| New common provider | 0 → 116 | +116 |
| G11 consumer | 138 → 27 | -111 |
| B10 consumer | 251 → 65 | -186 |
| Complete phase | 389 → 208 | -181 |

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,802 | 1,803 | +1 |
| Main effective lines | 202,207 | 202,026 | -181 |
| Li–Liu closure modules | 1,431 | 1,432 | +1 |
| Li–Liu closure effective lines | 194,652 | 194,471 | -181 |
| Chen closure effective lines | 99,260 | 99,260 | 0 |

All 116 shared-provider lines, imports, retained old proofs and new specialization
code are counted. Main physical lines change by -181 and
UTF-8 bytes by -8,307. The shared provider is in the Li–Liu closure
and outside the Chen closure; Chen's complete module/line/byte totals are unchanged.
Shared dependencies count independently in each theorem closure. External Lake
dependencies are excluded. No production proof moves into research or outside
the measured main tree. No auxiliary Lean code is added: the existing 17-line
internal-statement contract is pinned and reused unchanged. This phase follows
187 lines saved in the preceding phase, making 368 main/Li–Liu lines across the
two phases. No minimality or build-speed claim is made.

## Acceptance

All nine gates pass: warning-free 1,803-module full source build (10,511 Lake jobs),
both public literal/axiom checks, unchanged internal-strengthening contracts,
five named-module kernel replays and script tests (115 passes, one optional
full-export fixture skip). Kernel replays cover `Goldbach.Theorem`,
`Goldbach.Checks`, `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and
`Goldbach.All` over rebuilt imports; independent replay of every imported module
is not claimed. All 1,809 main source/configuration/checker pins and the separately
pinned statement probe match after each gate. The inventory gains exactly one
main Lean module. The complete census preserves all 10,405 old public names,
kinds and type hashes, with no missing declarations or added public declarations.

All three complete provider/consumer prototypes passed warning-as-error
compilation before application. Consumer prototypes use the actual common proof
block, without forward assumptions; the complete production import combination
is accepted by the separate full build. An initial B10 simplifier draft failed
to normalize `2*2` to `4`; the accepted proof explicitly normalizes that numeral.
No failed prototype supplies accepted evidence.

All six public endpoints preserve their exact constants and quantifier order:
`D19`, prime conditions, `r^10 ≤ q^9`, the genuine real exponent, Liu's singular
series, strict `1/2500`, fixed `κ < 515093/800000000` before the threshold and
Chen's `0.67`. Public axioms remain only `propext`, `Classical.choice` and
`Quot.sound`. The original final-cone producer guard, numerical grids, precision,
error constants and release checks are unchanged. Fresh Blueprint extraction,
local rendering, source positions, graph, annotations and tests pass:
68 nodes, 120 edges, four chapters and all six original exits.

This is an uncommitted local snapshot. Separate concurrent `research/wu2008`
sources, certificates and documentation are outside this proof phase. Historical
source-size cohorts are retained separately from current totals.

See [validation](../research/liliu-gate-budget-cleanup/validation.json),
[pinned inputs](../research/liliu-gate-budget-cleanup/validation-inputs.json),
[type preservation](../research/liliu-gate-budget-cleanup/type-preservation.json),
[all source changes](../research/liliu-gate-budget-cleanup/changes.json),
[moved public proofs and actual reference](../research/liliu-gate-budget-cleanup/moved-public-proofs.json),
[removed private stages](../research/liliu-gate-budget-cleanup/removed-private-proofs.json),
[retained private types](../research/liliu-gate-budget-cleanup/retained-private-statements.json),
[source sizes](../research/liliu-gate-budget-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-gate-budget-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-gate-budget-cleanup/reproduce.py --output /tmp/liliu-gate-budget-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` requests separate checks of a stable rebuilt Wu tree.
No saving from unimplemented follow-up candidates is included.
