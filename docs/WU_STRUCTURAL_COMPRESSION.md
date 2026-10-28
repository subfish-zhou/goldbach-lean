# Wu 1+1.8938 structural compression

This accepted phase removes 124 unused definitions, separates lightweight data and analytic interfaces, shares Jurkat/Bessel/log-grid arguments, and replaces a duplicated prime-counting/PNT route by the existing qualitative route. The net reduction, including new modules, is **7,612 effective Lean lines**, **9,092 physical lines**, and **467,539 bytes**. Mathematical grids, certificate precision, error budgets and final statements remain unchanged.

| Scope | Modules before → after | Effective lines before → after | Physical lines before → after |
|---|---:|---:|---:|
| Full Wu research tree | 4,142 → 4,151 | 573,895 → 566,283 | 677,021 → 667,929 |
| Final theorem import closure | 3,755 → 3,764 | 533,141 → 525,529 | 630,543 → 621,451 |

The previous 383-lemma phase saved 10,924 effective lines. Together these two phases save 18,536 lines. Against the original 1,126,636-line theorem closure, the cumulative reduction is 601,107 lines. Counts include entire imported local modules and do not measure a minimal declaration-level proof.

All 4,151 source contexts passed: 3,500 actual compiled source receipts (196 genuinely reused prefix proofs and 3,304 fresh V7 compilations), plus 651 verified unchanged dependencies. Acceptance compared 736 retained types and 183 data values. Of the values, 179 match raw expressions exactly; four contain generated proof parameters whose names changed. For those four, two strictly compiled and independently kernel-checked libraries prove equality to the same reference definitions at exactly 13 proof positions. The strict original mismatch and failed earlier builds remain archived. This does not permit changes to computational data.

The 78 acceptance gates include 65 fresh modified/final module kernel checks, five literal/standard-axiom reports and generator reproduction. After installation, the production tree passed the complete 4,151-module recursive receipt check, both the `one8938` and `one894` literal statements and standard axioms, and a fresh final-module kernel replay with the pinned toolchain. See the [machine-readable acceptance](../research/wu-structural-compression-audit/validation.json) and [actual production report](../research/wu-structural-compression-audit/production-verification.json).

Hf4 constructive DAG and uniform semantic/seed proofs are separate ongoing candidates. Their estimated savings are excluded here. The completed zero-incoming-reference census is likewise a prerequisite for further review, not permission to delete public declarations or an accepted code reduction.
