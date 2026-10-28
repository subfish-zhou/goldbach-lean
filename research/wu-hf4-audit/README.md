> Historical accepted snapshot. Current acceptance is in [the cumulative-table audit](../wu-table-audit/README.md).

# Hf4 exact-kernel compression audit

See the [mathematical and size report](../../docs/WU_HF4_COMPRESSION.md).
This phase follows the [structural simplification snapshot](../wu-structural-audit/README.md).

The original `kernel`, `endpointCellMass`, aggregated Q and final theorem are
unchanged. A Cayley-coordinate/Horner rational expression is proved equal to
the old kernel on its integration interval. Shared rational model lemmas replace
repeated real-arithmetic side-condition proofs. All finite arithmetic checks use
Lean's kernel, not native evaluation.

## Preserved contracts and size

- `baseline-source-index.json` records the preceding accepted source hashes,
  imports and line counts.
- `baseline-panel-statements.json` records all 40 original panel statements.
- `measure.py` checks those statements, source scope, unchanged aggregate/endpoint
  files and banned tokens in modified/new sources; `source-size.json` includes
  all four new helpers and removal of the old DAG.
- `certificate-enclosures.json` records exact old/new rational intervals.
  All new intervals lie strictly inside the original intervals. The same 40-cell
  grid, cubic order, 10^-14 rounding scale and radical interval are used.
- The full tree loses 50,995 effective Lean lines and 52,467 physical lines.
  The standalone Python generator, documentation and audit material are excluded
  from the Lean source metric. Module count rises from 4,771 to 4,774.
- Original internal generated `p`, `e`, `h` and DAG declarations are replaced;
  the audit preserves the panel mass bounds and downstream mathematical APIs,
  not every obsolete generated declaration.

## Evidence

`validation.json` records final acceptance and hashes of the evidence:

- `full-build.log`: all 4,774 source/object/dependency receipts validated, with
  affected modules compiled. Unchanged objects are reused only with matching
  receipts; this is not a forced clean rebuild.
- `literal-check.log`, `classical-acceptance.json`, `classical-literal-axioms.log`:
  exact 1.8938 and legacy 1.894 statements and standard classical axioms.
- `kernel-*.log`: independent replay of the compact-kernel identity, integration
  bridge, rational soundness helper, one complete panel, and final theorem over
  the accepted imports. Not an independent replay of every imported module.
- `generator-check.log`: all 15 generated files reproduced exactly.
- `verify-sources.log`: source/history bytes and manifest coverage.

## Reproduction

From the repository root:

```sh
python3 research/wu2008/diagnostics/hf4_compact_certificates.py --output-dir research/wu2008/src --check
python3 research/wu2008/build.py --all --jobs 3 --lean-threads 2
python3 research/wu2008/check_classical.py
python3 research/wu2008/verify_sources.py
python3 research/wu-hf4-audit/measure.py
```

The generator is self-contained Python using exact `Fraction` arithmetic; its
output is checked by Lean. Historical audit directories retain their original
accepted snapshots and should not be mistaken for current source inventories.
