# Public 1+1.8938 and the second precision-preserving compression

See the [report](../../docs/WU_18938_COMPRESSION.md). This phase is measured
against the previous accepted 5,441-module tree, whose final theorem closure
contained 755,925 effective code lines. The initial 8,826-module baseline is
reported separately as a cumulative comparison.

`baseline-source-index.json` preserves the previous tree's per-module hashes,
imports and line/byte counts, captured from its source archive before edits.
Run `python3 research/wu18938-audit/measure.py` to compare the current sources
against that index. The script includes additions, shared helpers and both
public endpoints. It asserts that only the stated generated cohort and the
two endpoint source modules change.

`generated-change-plan.json` identifies the cohort and the unchanged tables.
`source-size.json`, `type-comparison.json` and `validation.json` record source
size, compiled declaration differences and final validation respectively.
The raw compiled censuses are local artifacts. Collect them using the previous
phase's `collect_types.py` into baseline/current subdirectories, then invoke
this phase's `compare_types.py` with their parent directory.

Old phase reports are historical snapshots; this directory is the evidence for
this phase. No build-time speedup or globally minimal proof is claimed.
