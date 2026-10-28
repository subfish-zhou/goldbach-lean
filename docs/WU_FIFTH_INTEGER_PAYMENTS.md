# Fifth-slot exact integer payment formulas

This phase follows [the lightweight numeric layers](WU_LIGHT_NUMERIC_LAYERS.md).
The final `WuPaper.ClassicalSlots.one8938` theorem, legacy `one894` interface,
original constants, grids and numerical precision are unchanged.

Three 1,024-entry payment tables are replaced by exact Nat formulas. The existing
12-term logarithm lower polynomial uses the shared homogeneous integer Horner
identity. The degree-12 signed cPoly is regrouped into five positive/negative
coefficient pairs with common denominator 52,254,720. On its original domain
0 ≤ Y ≤ D, each pair satisfies b*Y ≤ a*D, so every Nat subtraction is exact.
This is an algebraic identity, not a new approximation or constant adjustment.
The original cPoly QName and expression move to a pure rational data module;
the real bridges and final Fifth Certificate remain unchanged.

The generic rational identity and Nat floor inequality replace 48 pointwise
GridBlock certificates. Three sum containers still check 48 independent
64-point sums using `decide +kernel`. Their original numerator totals are
273358482524540, 661191362320992 and 405237426677551, with payment scale 10^12.
All 3,072 original payments and the zero outside-support guard are preserved.

| Scope | Effective lines before | Effective lines after | Reduction |
|---|---:|---:|---:|
| Full local Wu tree | 588,598 | 584,819 | 3,779 |
| Final theorem import closure | 547,844 | 544,065 | 3,779 |

The full tree contains 4,142 modules and 688,537 physical lines;
the theorem closure contains 3,755 modules and 642,059 physical
lines. Net savings include all new helpers: 39 modules, 3,699 physical lines
and 94,637 bytes. External Lake packages are excluded. These count
whole imported modules, not minimum declaration-level proofs.

The full source/receipt build, literal statements and standard axioms, four
generators, independent actual-source Nat interpretation, preservation checks,
9 negative controls and 9 named kernel replays pass. The interpreter
checks actual Lean formula syntax, including clipped Nat subtraction and
division-by-zero semantics, against frozen original tables. This Python check
supplements Lean proof/kernel checking. Unchanged receipts may be reused after
dependency validation; this is not a forced clean build or a claimed speedup.

See [the accepted audit](../research/wu-fifth-integer-audit/validation.json) and
[reproduction commands](../research/wu-fifth-integer-audit/README.md).
