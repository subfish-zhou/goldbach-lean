# Wu derived tables and shared correction certificates

This phase preserves the public 1+1.8938 theorem, its legacy 1+1.894 corollary,
all original numerical payments, grids, rounding scales and logarithm orders.
It follows the [previous cumulative-table compression](WU_TABLE_COMPRESSION.md).

## Mathematical changes

The fourth term's outer samples are determined by B and D. Storing another
10,541 integers and separately verifying them adds no independent mathematical
information. The new definition is exactly

\[
q_i=\left\lceil\frac{2654\cdot4000^2(10^{15}+B_i+T_i)}
{(12000+i)(5308000-200(12000+i))}\right\rceil,
\qquad T_i=\begin{cases}D_{i-8000}&i\ge8000,\\0&i<8000.\end{cases}
\]

The denominator is positive throughout the original grid. One division/remainder
lemma establishes all outer sample inequalities, replacing 42 finite-check
modules. Out-of-range samples still return zero.

The C and D cumulative tables are also determined by exact integer recurrences.
Their endpoint samples are upward-rounded divisions of the preceding table:
`ceil(4000*parent(i)/(base+i))`, with base 12000 or 16000. These samples feed the
same rounded trapezoid increment as before. Every fourth original cumulative
value remains an anchor, bounding reconstruction to three steps. Multiplying
the endpoint ceiling inequalities by positive denominators proves the original
CPay/DPay inequalities without introducing new error allowances. Finite checks
remain only at anchor joins. The finite support is unchanged.

The eighth correction already has an exact affine-integral lower bound. Its
repeated point proofs are replaced by one rational-to-real soundness theorem
and finite rational checks. The original 512 payments, 10^12 scale, twelve-term
logarithm and final lower bound 194378/10^7 are unchanged.

These are changes to proof representation and shared mathematical arguments;
none improves the final exponent by tuning constants.

## Measured reduction and verification

| Scope | Before effective lines | After effective lines | Net reduction |
|---|---:|---:|---:|
| Full local Wu tree | 646,015 | 625,805 | 20,210 |
| Final theorem import closure | 605,261 | 585,051 | 20,210 |

The full tree contains 4,641 modules and 731,546 physical
lines; the theorem closure contains 4,254 modules and
685,068 physical lines. Counts include all new shared lemmas.
The cumulative closure reduction from the original version is 541,585
effective lines. This is module-level source size, not a minimal declaration
proof size.

The complete source/receipt build passes. Unchanged objects may be reused only
when their source and dependency receipts match. Both independent literal
statements (1.8938 and 1.894) and standard-axiom checks pass. Independent kernel
replays cover the new arithmetic/soundness helpers, fourth concrete assembly
and final theorem over accepted imports. The source verifier, both generators,
352 retained theorem-statement contracts, and exact comparisons against
the original Git tables pass (36,705 reconstructed values, plus unchanged Bq).
These are complementary checks: Python equality
checks do not replace Lean's proofs.

The original outerq-only benchmark increased representative outer payment block
times from 8.32 to 13.17 seconds and 6.46 to 8.00 seconds. Reconstructing values
trades some reduction time for smaller sources; the full build verifies the
combined C/D and outerq implementation. A separate 256-point outer payment
benchmark starting at index 8192, with full D-to-C-to-B reconstruction, took
87.97 seconds. The nested representation has a material compilation cost;
this is a source-size optimization, not a claimed build-speed improvement.
The isolated timing does not predict wall time under concurrent load;
`full-build.log` records the accepted serial continuation timings.
The accepted full build uses one compilation worker after observed memory
contention under concurrent workloads. No constant or precision was relaxed.

See [the reproducible audit](../research/wu-derived-audit/README.md).
