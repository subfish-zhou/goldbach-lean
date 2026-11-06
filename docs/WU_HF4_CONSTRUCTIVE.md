# Wu 1+1.8938: constructive Hf4 certificates

The installed change replaces the repeated per-cell certificate chains by one sound interpreter that constructs addition, multiplication and reciprocal approximants. Numerical precision, `D = 10^14`, all 40 original mass-bound statements and all 80 endpoint targets remain unchanged. The final theorem is still `r ^ 5000 ≤ q ^ 4469`, with the legacy 1.894 theorem retained.

| Scope | Modules before → after | Effective lines before → after | Physical lines before → after |
|---|---:|---:|---:|
| Full Wu source inventory | 4,151 → 4,151 | 566,283 → 540,985 | 667,929 → 629,373 |
| Final theorem import closure | 3,764 → 3,764 | 525,529 → 500,231 | 621,451 → 582,895 |

The measured saving is **25,298 effective lines**, **38,556 physical lines**, and **2,759,754 bytes**, including new modules. It includes the uniform semantic proof's 2,204 lines and rational-seed proof's 254 lines. Against the original 1,126,636-line closure, the cumulative saving is 626,405 lines. Counts include whole local proof modules, excluding external packages and historical/generator copies.

## Mathematical construction

A rational cubic `p(x) = a + bx + cx² + dx³` with error `e` bounds `|f(x) - p(x)|` throughout `|x| ≤ 1`. The same invariant is proved once and propagated along the program. Addition and multiplication compute rounded coefficients and round the required error upward. The multiplication residual includes degrees four through six; these terms are not discarded when the stored polynomial remains cubic.

For reciprocals, `L = |a| - |b| - |c| - |d| - e > 0` bounds the absolute value of `f` away from zero; `f` need not itself be positive. The constructor obtains a rational cubic `q` from the truncated inverse-series recurrence. Its error is certified by

\[
 \left|\frac1f-q\right|
 \le \frac{\operatorname{residual}(pq-1)+\|q\|e}{L}.
\]

The [constructors](../research/wu2008/src/Hf4ConstructionConditions.lean) round this bound upward at the original precision. The [interpreter](../research/wu2008/src/Hf4ConstructiveDagData.lean) accepts no literal-certificate function or intermediate payload table; its arithmetic checker needs only the positive-lower reciprocal guards. [Generic soundness](../research/wu2008/src/Hf4ConstructiveDagSoundness.lean) follows by induction over the program. The [table interface](../research/wu2008/src/Hf4ConstructiveTableData.lean) computes final certificates and verifies their original endpoint targets.

Direct algebra reduces the program from 381 to 371 nodes. All **74,200 intermediate fields are computed**, rather than retained as a remaining payload table; they must not be counted a second time as future removable data. The 47 shared seeds and 80 endpoint bounds remain inputs. The uniform seed proof handles 45 exact rational seeds generically and retains the two radical arguments.

## Actual acceptance

All 4,151 source contexts passed: 389 actual proof receipts (53 verified original prefix proofs plus 336 subsequent compilations) and 3,762 unchanged dependencies. The isolated 25-step acceptance compared 696 retained types and all 183 selected definition expressions exactly, checked both final literal statements and standard axioms, replayed 19 candidate/final kernels, reproduced the generator and rechecked all contexts. No new proof-irrelevance bridge or numerical tolerance was used in the data comparison.

The 40 obsolete compact-model interfaces were deliberately retired with their old 17-module implementation; the 40 public mass-bound interfaces retain their exact original written statements and elaborated types. After transactional installation, production generator reproduction, all 4,151 recursive receipts, literal/axiom checks and a fresh final-module kernel replay passed. See the [acceptance record](../research/wu-hf4-constructive-audit/validation.json) and [production report](../research/wu-hf4-constructive-audit/production-verification.json).

The new producer is self-contained and uses relative frozen inputs, with relocated read-fence and mutation tests. Run `python3 research/wu2008/diagnostics/hf4_constructive/produce.py --route constructive --output-dir research/wu2008/src --check`. Earlier Hf4 audit directories remain historical snapshots. The separate public/private unused-proof candidates remain pending and are excluded from the accepted reduction.

The subsequent [unused-proof pruning](WU_UNUSED_PROOF_PRUNING.md) saves another
31,209 effective lines. This document and its phase acceptance JSON remain
historical Hf4 snapshots; current measurements are in the subsequent audit.
