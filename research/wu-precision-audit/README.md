# Precision-preserving Wu certificate compression

This is the accepted first-phase snapshot. Current acceptance is in
[the second-phase audit](../wu18938-audit/README.md).

The [report](../../docs/WU_PRECISION_COMPRESSION.md) explains the mathematical
scope, source reduction and verification. Baseline: commit
`c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`; only the Wu subtree is compared.

- `source-size.json`: whole-tree and final import-closure counts, including all
  four new shared modules, with the complete changed/new/deleted module lists.
- `source-invariants.json`: unchanged analytic sources and byte-identical numeric
  tables; lexical prohibited-token scan is supplementary to Lean validation.
- `generated-change-plan.json`: the three generator families before and after.
- `type-comparison.json`: retained public declaration kind/type comparison;
  changed internal finite-block types are reported explicitly.
- `validation.json` and logs: build, literal/axiom, generator and targeted kernel
  replay evidence. Historical initial-integration reports remain historical.

Run `check_source_invariants.py` and `measure.py` with Python from any directory;
these use the Git baseline and current source files. Type comparison needs
compiled objects from both snapshots. Build each snapshot in its own checkout,
then use `collect_types.py WU_DIRECTORY OUTPUT/baseline` for the original and
`collect_types.py WU_DIRECTORY OUTPUT/current` for the new tree. Run
`compare_types.py OUTPUT` afterward. The census utility reads Lean ModuleData
without running imported extensions; the large raw censuses are local build
artifacts, not proof inputs.

`measure.py`, `check_source_invariants.py` and `compare_types.py` write their
corresponding reports here. Re-running them after later source changes produces
a new measurement, not evidence for the original accepted snapshot. This audit
does not measure a minimal declaration-level proof or establish a build-time
speedup.
