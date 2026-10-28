# Sixth exact integer payment formulas

This phase compresses both Sixth integral payment certificates and follows
[C integer payments](WU_INTEGER_PAYMENTS.md). The public theorem
remains 1+1.8938, with the legacy 1+1.894 interface retained.

## What changes mathematically

The existing twelve-term logarithm approximation is written as a homogeneous
integer polynomial using the common odd denominator 334639305. The unchanged common lemma
proves its identity with the original rational sum. Horner evaluation keeps the
polynomial compact; the high-degree identity is proved in abstract coordinates
before substituting midpoint expressions.

Payments are now integer quotients computed from this exact formula. A general
rounding lemma proves the payment inequality for every grid index. The finite
proofs retain independent 64-point sum checks, grouped into modules to avoid
repeatedly loading the same dependencies. They establish the original totals.
All 8192 original Sixth payments and all 128 block sums remain exact. The
lower and upper totals remain 939922834048256 and 1025832247091325.
The C certificate and shared Horner helper remain byte-identical.

Large-integer boundary proofs are factored into opaque lemmas over abstract
variables before grid substitution. This prevents expensive definitional
conversion in the kernel without changing any bound or numerical constant.
No logarithm term, grid point, rounding precision or numerical bound is removed.
The old literal payment tables and individual point-check modules disappear.

## Measured size

| Scope | Effective lines before | Effective lines after | Net reduction |
|---|---:|---:|---:|
| Full local Wu tree | 615,278 | 604,478 | 10,800 |
| Final theorem import closure | 574,524 | 563,724 | 10,800 |

The full tree contains 4,459 modules and 708,195 physical lines.
The theorem closure contains 4,072 modules and 661,717
physical lines. Its cumulative saving is 562,912 effective lines.
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

See [the audit](../research/wu-sixth-integer-audit/README.md) for reproducible commands,
exact numerical comparison scope, module counts and evidence hashes.
