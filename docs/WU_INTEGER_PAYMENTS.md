# Exact integer payment formulas

This phase compresses the C integral payment certificate only and follows
[Hf4 sharing](WU_SHARED_CERTIFICATES.md). The public theorem
remains 1+1.8938, with the legacy 1+1.894 interface retained.

## What changes mathematically

The existing twelve-term logarithm approximation is written as a homogeneous
integer polynomial using the common odd denominator 334639305. A shared lemma
proves its identity with the original rational sum. Horner evaluation keeps the
polynomial compact; the high-degree identity is proved in abstract coordinates
before substituting midpoint expressions.

Payments are now integer quotients computed from this exact formula. A general
rounding lemma proves the payment inequality for every grid index. The finite
proofs retain independent 64-point sum checks, grouped into modules to avoid
repeatedly loading the same dependencies. They establish the original totals.
All 4096 original C payments, all 64 block sums, and the total
207693136875355 remain exact. The Sixth prototypes are not part of this phase.
No logarithm term, grid point, rounding precision or numerical bound is removed.
The old literal payment tables and individual point-check modules disappear.

## Measured size

| Scope | Effective lines before | Effective lines after | Net reduction |
|---|---:|---:|---:|
| Full local Wu tree | 620,401 | 615,278 | 5,123 |
| Final theorem import closure | 579,647 | 574,524 | 5,123 |

The full tree contains 4,583 modules and 718,960 physical lines.
The theorem closure contains 4,196 modules and 672,482
physical lines. Its cumulative saving is 552,112 effective lines.
Counts include the shared helper and all replacement proof modules, but exclude
external Lake packages, Python generators and audit material. They count whole
imported modules, not minimal declaration-level proofs.

## Validation

The full source/dependency receipt build, both independent literal theorem and
standard-axiom probes, and source verification pass. Unchanged objects may be
reused only with matching receipts; this is not a forced clean build.
Independent kernel replay scope is listed explicitly in the audit record.

Independent exact arithmetic compares formula-generated payments with the
SHA-bound tables in the fixed Git baseline. Generator byte checks and retained
mathematical statement checks supplement Lean verification. The final theorem
source and preserved Hf4/Eighth data remain byte-identical to the preceding
accepted snapshot. No constant was retuned.

See [the audit](../research/wu-integer-audit/README.md) for reproducible commands,
exact numerical comparison scope, module counts and evidence hashes.
