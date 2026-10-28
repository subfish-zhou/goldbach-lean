# Wu 1+1.894: certificate compression with preserved precision

This page records the accepted first compression phase. See the [second-phase 1+1.8938 report](WU_18938_COMPRESSION.md) for the current public result and further compression.

This phase preserves the internal counting parameter `9469/5000 = 1.8938`, all
integration meshes, logarithm expansion orders, rounding denominators and error
budgets. The accepted public conclusion remains
`WuPaper.ClassicalSlots.one894`; no separate literal acceptance of the 1.8938
statement is asserted.

## Compression method

The original certificates repeatedly expanded real formulas, substituted
integer numerators and proved the resulting inequalities at every node. The
new implementation expresses these formulas exactly over the rationals, proves
once that their embeddings into the reals equal the original formulas, and
checks each comparison in the finite tables with `decide +kernel`. Python
produces candidate values and Lean sources; it does not bypass Lean proof
checking.

Four small modules are added:

- `WR2ExactRationalLog`: rational versions of the original twelve-term logarithm
  bounds, their embedding identities and the original remainder terms.
- `WR2ClassicalFourthTableCheck`: exact rational comparisons and their
  correctness proofs for the fourth-term upper bound.
- `WR2ClassicalFifthTableCheck`: comparisons and correctness proofs for the
  fifth-term correction polynomial and the three midpoint formulas.
- `WR2ClassicalSixthTableCheck`: comparisons and correctness proofs for the two
  sixth-term midpoint formulas.

The numerical tables and summation ranges are unchanged. The fourth-term
integer checks compile in blocks of 256 entries and its logarithm checks in
blocks of 64; the fifth and sixth terms use blocks of 64. These are compilation
block sizes, not integration mesh sizes.

| Certificate family | Original generated modules | Current generated modules | Preserved numerical parameters |
|---|---:|---:|---|
| Classical fourth term | 2,480 | 323 | Step `1/4000`, original node count, denominator `10^15` |
| Classical fifth term | 391 | 55 | Three sets of 1,024 midpoints, denominator `10^12` |
| Classical sixth term | 1,029 | 133 | Two sets of 4,096 midpoints, denominator `10^12` |
| Total | 3,900 | 511 | Twelve-term logarithm expansion and original error bounds |

The old fourth-term generator also produced an extra coverage root that was
never integrated into the source tree. The baseline counts only the 2,480
modules actually present; this unintegrated file is not credited as a deletion.
The other 4,926 original modules are byte-for-byte unchanged, as are all eleven
original numerical tables. Their SHA-256 hashes are recorded in the
[invariant checks](../research/wu-precision-audit/source-invariants.json).

## Net size and acceptance

The baseline is the Wu source tree at
`c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`. It matched that revision at the start
of this phase. New common lemmas are included in the compressed totals, so
moving code into common modules is not counted as a deletion. Effective code
lines exclude blank lines and comments, preserve strings, and exclude external
Lake dependencies.

| Scope | Modules: before to after | Effective code lines: before to after | Net reduction |
|---|---:|---:|---:|
| Final theorem import closure | 8,444 to 5,059 | 1,126,636 to 755,925 | 370,711 (32.90%) |
| Complete research tree | 8,826 to 5,441 | 1,166,974 to 796,263 | 370,711 (31.77%) |

The complete research tree falls from 1,303,650 to 911,671 physical lines, a
reduction of 391,979 lines and 30,307,523 UTF-8 bytes. The net module reduction
is 3,385, after counting the four added modules.

See the [machine-readable measurements](../research/wu-precision-audit/source-size.json).
The final theorem import closure and complete research tree are measured
separately. Module totals include definitions, statements, commands and proofs;
they do not measure a minimal declaration-level proof.

Acceptance passes the complete 5,441-module build and source/object/dependency
receipt checks, the final literal-statement and standard-axiom checks, and
independent kernel replays of the final module and four new common modules.
The three generators exactly reproduce all 323, 55 and 133 modules respectively.
The source scan finds no `sorry`, new axiom declarations, `native_decide` or
`unsafe`.

Compiled declaration comparisons preserve the kinds and types of 223,214
retained public declarations, including 222,046 from non-generated modules.
The compilation block-size change alters the types of 487 internal finite-block
declarations and 28 automatically generated coverage helpers. Pointwise redundant
declarations and excess blocks disappear with their files. The final theorem,
aggregate bounds and non-generated mathematical interfaces are unchanged. Here
"public declaration" means a declaration whose Lean name is not private; it
does not make every internal certificate block a stable API.

The [acceptance record](../research/wu-precision-audit/validation.json) and
[type comparison](../research/wu-precision-audit/type-comparison.json) specify
the scope. The independent replays cover those five modules over imports
verified by the complete build; five replays do not mean every imported module
was independently replayed again.

## Reproduction

At the repository root:

```sh
python3 research/wu-precision-audit/check_source_invariants.py
python3 research/wu-precision-audit/measure.py
```

In `research/wu2008`:

```sh
python3 diagnostics/classical_fourth_certificates.py --check src
python3 diagnostics/classical_fifth_certificates.py --check src
python3 diagnostics/classical_sixth_certificates.py --check src
python3 verify_sources.py
python3 build.py --all --jobs 4 --lean-threads 2
python3 check_classical.py
```

The [research README](../research/wu2008/README.md) gives the independent replay
commands. Original object fingerprints in the source manifest remain historical
collection records; `build/receipts` verifies the current rebuilt objects against
their sources and dependencies.

This phase increases neither numerical precision nor the mathematical constants.
The common rational lemmas can support future candidate tables at higher
precision, but new tables, error estimates and final budgets must be verified
again. Other generated certificates and historical research entries remain;
these results do not establish that the proof is minimally sized.
