# Eighth raw integral: exact upper-log payments

This phase follows [Sixth compression](WU_SIXTH_INTEGER_PAYMENTS.md). The
public theorem remains 1+1.8938, and the legacy 1+1.894 interface is retained.

The original upper logarithm approximation is expressed as an exact integer
fraction using the existing homogeneous Horner polynomial. Its original
remainder is **2*z^25/(1-z²)**, with no extra denominator 25. The proof keeps
high-degree algebra in abstract variables before substituting grid coordinates.

A shared ceiling inequality proves every payment is an upper bound. Independent
64-point sum checks establish all 32 original block totals. All **2048** payments
retain their exact values, and their numerator sum remains **5258450040652036**.
The original scale, midpoint grid, integration error and raw integral bound are
unchanged. The separate Eighth correction certificate is byte-identical, as are
the C/Sixth sources and existing Horner and cumulative-division helpers.

| Scope | Effective lines before | Effective lines after | Net reduction |
|---|---:|---:|---:|
| Full local Wu tree | 604,478 | 601,997 | 2,481 |
| Final theorem import closure | 563,724 | 561,243 | 2,481 |

The full tree contains 4,431 modules and 705,772 physical lines.
The final theorem closure contains 4,044 modules and
659,294 physical lines. Its cumulative saving from the original
version is 565,393 effective lines. Counts include all new proof helpers
and whole imported modules; external Lake packages, generators and audit files
are excluded. These are not minimal declaration-level proof lengths.

The full source/dependency receipt build, literal theorem and standard-axiom
checks, generator byte checks and source verifier pass. Independent kernel
replays cover the named modules in the audit. Unchanged objects may be reused
only with matching receipts; this is not a forced clean build.

An independent source-bound integer calculation compares every payment and
block target with the SHA-bound historical tables. This complements Lean
verification. The final theorem source remains byte-identical; no constant or
precision was adjusted. See [the audit](../research/wu-eighth-integer-audit/README.md).
