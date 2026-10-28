# Lightweight numeric layers and grouped payment modules

This phase follows [the exact Fourth Bq formula](WU_FOURTH_BQ_FORMULA.md).
It preserves the 1+1.8938 theorem, the old 1+1.894 interface, all precision,
constants, numerical producer functions, and the original payment proofs.

Pure rational definitions and natural-number payment predicates now live in
separate modules. Their real-analysis bridges import these modules. Numeric
checks therefore do not load the local number-theory development merely to
state integer inequalities. This changes numeric compilation dependencies;
the final theorem still requires its original analytic arguments.

The 104 individual Fourth payment proofs are placed in 16 containers of at
most eight proofs each. Every original statement, proof, qualified name and
local checking budget is preserved byte for byte. Four unchanged aggregation
proofs reference all 104 component proofs, and their axiom prints cover those
dependencies. No single large decision procedure replaces the individual proofs.

| Scope | Effective lines before | Effective lines after | Reduction |
|---|---:|---:|---:|
| Full local Wu tree | 589,115 | 588,598 | 517 |
| Final theorem import closure | 548,361 | 547,844 | 517 |

The full tree contains 4,181 modules and 692,236 physical
lines. The final theorem closure contains 3,794 modules and
645,758 physical lines. These counts include replacement helpers,
exclude external Lake packages, and count whole imported modules.

Receipt reuse now binds the full transitive dependency context, including
source and object hashes. An independent replay caught an old object referring
to a removed transitive import; the cache rule was corrected, 55 affected
receipts were invalidated, and the retained ancestor-closed receipts were
explicitly audited. The unchanged source passed a fresh compile and replay.
Eighteen build-driver regression tests cover this failure mode and prior checks.

The complete source/receipt build, literal theorem and standard-axiom checks,
three generator checks and 12 named independent kernel
replays pass. Unchanged objects may be reused only with matching dependency
receipts; this is not a forced clean build. Source preservation includes nine
negative controls and unchanged numerical producer ASTs.

Before adoption, a fresh isolated 15-module strict compilation passed. Its
single heavy outer payment block used 6,072,424 KiB peak RSS, compared with
12,181,036 KiB in the previous heavy-import run; wall time was 57.635 versus
52.925 seconds. The eight-proof container passed in 366.007 seconds with
6,845,768 KiB peak RSS. These single-run observations do not establish full-build
speed improvements. See [the probe](../research/wu-light-layer-probe/validation.json)
and [the accepted audit](../research/wu-light-layer-audit/validation.json).
