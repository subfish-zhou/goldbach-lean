# Cumulative-table and exact-certificate audit

See [the mathematical and size report](../../docs/WU_TABLE_COMPRESSION.md).
The preceding accepted snapshot is [the Hf4 audit](../wu-hf4-audit/README.md).

This phase preserves the 1.8938 theorem, original grids, rounding scales and
numerical bounds. Fourth-slot cumulative values are reconstructed exactly;
sixth-source payments are certified without intermediate rounding; seventh and
ninth point proofs are replaced by shared exact-rational checks.

## Contracts and counts

- `baseline-source-index.json` contains pre-phase source hashes, imports and sizes.
- `baseline-statements.json` preserves 120 downstream theorem statements.
- `measure.py` checks those statements, modified-source scope and banned tokens,
  and counts all added helpers. `source-size.json` separates the four families.
- `contracts.json` records byte-preserved seventh/ninth data and sum proofs plus
  the first 36 statement comparisons. The complete 120-statement check is in
  `measure.py`.
- `check_values.py` reads original tables from fixed Git commit
  `c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`, verifies the original source hashes,
  and compares every value reconstructed from current-source anchors. It requires
  that Git history object. `value-comparison.json` records 21,082 exact matches
  and preservation of the out-of-range zero convention. This is an exact Python
  integer audit, not a Lean proof; Lean independently checks the retained bounds.
- 4,574 pre-existing source files are byte-identical. Removed internal point,
  panel and data-block declarations are not claimed as preserved public APIs.

The full Lean tree and final theorem closure each lose **31,655 effective lines**
and **33,295 physical lines**, including all new helpers. The full inventory is
4,713 modules and the theorem closure is 4,326 modules. Python generators,
documentation, audit files and external Lake packages are excluded from these
Lean-source counts.

## Verification records

`validation.json` gives the final acceptance status and hashes of evidence:

- `full-build.log`: complete source/object/dependency receipt validation and
  compilation of affected modules; unchanged objects may be reused only when
  their receipts match. This is not a forced clean rebuild.
- `literal-check.log`, `classical-acceptance.json`, `classical-literal-axioms.log`:
  exact 1.8938 and legacy 1.894 statements and standard classical axioms.
- `kernel-*.log`: independent replays of the seventh, ninth and sixth rational
  soundness helpers, cumulative payment theorem, fourth-slot concrete assembly,
  and final theorem over the accepted imports. Not every import is individually
  replayed.
- `generator-*.log`: unchanged generated output reproduced by four generators.
- `verify-sources.log`: source/history integrity and manifest coverage.

## Reproduce

From the repository root:

```sh
python3 research/wu2008/build.py --all --jobs 2 --lean-threads 2
python3 research/wu2008/check_classical.py
python3 research/wu2008/verify_sources.py
python3 research/wu-table-audit/measure.py
python3 research/wu-table-audit/check_values.py
python3 research/wu2008/diagnostics/classical_seventh_certificates.py --check
python3 research/wu2008/diagnostics/classical_ninth_certificates.py --check
python3 research/wu2008/diagnostics/sixth_source_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_fourth_certificates.py --check research/wu2008/src
```

Historical audits retain their original source snapshots and scope.
