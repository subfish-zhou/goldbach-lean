# Fourth Bq: exact split-log ceiling formula

This phase follows [Eighth compression](WU_EIGHTH_INTEGER_PAYMENTS.md). The
public 1+1.8938 theorem and legacy 1+1.894 interface remain unchanged.

The Bq table is replaced by an exact integer expression for its original split
upper logarithm, followed by the original ceiling operation at scale 10^15.
The two Cayley fractions share numerator i and have denominators 16000+i and
16000+3i. A general rational identity and the existing ceiling inequality prove
the bound for every supported index, replacing the 165 individual Log blocks.

All **10541** original values remain exact. In particular, index zero is an
exact quotient and stays zero; floor-plus-one would change it and is not used.
Out-of-support values remain zero. The original cumulative anchors, their
spacing, analytic errors and final integral bounds remain byte-identical.
No logarithm remainder, numerical precision or constant is retuned.

| Scope | Effective lines before | Effective lines after | Net reduction |
|---|---:|---:|---:|
| Full local Wu tree | 601,997 | 589,115 | 12,882 |
| Final theorem import closure | 561,243 | 548,361 | 12,882 |

The full tree contains 4,267 modules and 692,732 physical lines.
The final theorem closure contains 3,880 modules and
646,254 physical lines. Its cumulative saving is 578,275
effective lines. Counts include all replacement helpers and whole imported
modules, excluding external Lake packages, generators and audit material.
They are not minimal declaration-level proof lengths.

The full source/dependency receipt build, literal theorem and standard-axiom
checks, generator byte checks and source verification pass. Independent kernel
replays cover the named modules in the audit. Matching receipts permit reuse of
unchanged objects; this is not a forced clean build.

The value audit binds the actual source formula and all original table values
to their SHA fingerprints. A representative downstream benchmark checks the
cost of repeated Bq evaluation through the existing B/C/D/outer recurrences;
its exact scope and single-run measurements are recorded in the audit.
See [the audit](../research/wu-fourth-bq-audit/README.md).
