# Hf4: construct approximants instead of supplying intermediate certificates

The current candidate already constructs **addition, multiplication and reciprocal** certificates. It does not retain a table of the 74,200 intermediate coefficient/error fields. That number describes computed fields, not remaining stored payloads. The 47 shared seeds, 80 original endpoint bounds and `D = 10^14` remain numerical inputs. This construction has now passed full project acceptance and installation; see the [current audit](../wu-hf4-constructive-audit/README.md).

## One pointwise invariant

A certificate consists of a rational cubic `p(x) = a + bx + cx² + dx³` and an error `e`. Its invariant bounds `|f(x) - p(x)|` by `e` throughout `|x| ≤ 1`. The same generic proof applies to every node and every cell.

[Construction conditions](candidate/Hf4ConstructionConditions.lean) compute the four rounded coefficients and round the required error upward. Addition pays coefficient rounding plus the input errors. Multiplication pays input errors and the complete degree-six product residual. In particular, degrees four through six are included in the residual; reducing the stored polynomial degree does not discard their contribution to the bound.

## A residual proves reciprocal correctness

For a valid approximation `p` of `f`, let `L = |a| - |b| - |c| - |d| - e`. The only numerical reciprocal guard is `L > 0`, which bounds **the absolute value** of `f` away from zero; it does not require `f` itself to be positive.

The constructor first obtains a rational cubic `q` from the truncated inverse-series recurrence and rounds its coefficients at the existing precision. The enclosure follows from

\[
 \left|\frac1f-q\right|
 \le \frac{\operatorname{residual}(pq-1)+\|q\|e}{L}.
\]

The numerator pays both the full polynomial residual and the input approximation error. Rounding this quotient upward gives the new error field. The validity argument depends on the residual bound, rather than a separately supplied reciprocal witness.

## A program induction replaces the repeated proof chains

The [constructive interpreter](candidate/Hf4ConstructiveDagData.lean) calls these constructors directly. Its signature has no literal-certificate function or intermediate payload parameter. Its checker returns `true` for the automatically justified operations and checks only strict positivity of the reciprocal lower bounds.

[Generic soundness](candidate/Hf4ConstructiveDagSoundness.lean) proves the pointwise invariant by induction over the program. The [table interface](candidate/Hf4ConstructiveTableData.lean) computes each final certificate from the same program and then checks its lower and upper mass bounds against the original targets. For a symmetric cell, the cubic integral uses the even coefficients `a + c/3`, with the existing interval scaling and error payment.

The direct algebra reduces the program from 381 to 371 nodes. Separately, the uniform semantic proof and the uniform rational-seed proof remove repeated proof cases. All 40 original written mass-bound headers and all 80 target inequalities remain unchanged.

The accepted source-scope measurement is 25,298 fewer effective Lean lines, including 2,204 from the semantic proof and 254 from the seed proof. These savings are included in the current accepted production totals. The 74,200 computed fields must not be counted again as a future removable table.
