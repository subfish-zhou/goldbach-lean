# Paused Hf4 constructive compression

**Historical pause/resume snapshot. The Hf4 construction has now been accepted and installed; see the [current audit](../wu-hf4-constructive-audit/README.md).** The descriptions below retain the earlier pause point and its then-provisional estimates. The separate public/private pruning candidates remain pending.

This directory preserves the complete mathematical source of the next candidate, its portable producer, actual partial compilation evidence, interface comparisons, successful and failed seed trials, and the separate private/public pruning candidates. Compiled objects and build caches remain local and are not repository source artifacts.

The constructive candidate replaces 17 old modules with 17 new modules and changes only the Aggregate import. It preserves all 40 original mass-bound headers, all 80 numerical endpoints, denominator 10^14 and 74,200 computed numeric fields; it constructs addition, multiplication and reciprocal certificates directly, with no intermediate literal-certificate payload table. The 74,200 fields are computed, not stored. See the [mathematical construction](MATHEMATICS.md). Its semantic proof saves 2,204 effective lines and its uniform rational seed proof saves 254. The combined candidate predicts **25,298 fewer effective lines**, including those two savings, and a final theorem import closure of **500,231 lines**. At this pause snapshot, those estimates had not been accepted; the subsequent full acceptance now records the actual installed savings.

Actual completed validation before pausing:

- All 40 constructive table checks compiled in the full candidate run.
- The uniform seed and semantic sources compiled strictly, 10 retained types and three data values matched exactly, two consumers recompiled, and three fresh consumer/seed kernel replays passed (the semantic module also has its earlier fresh replay).
- All 17 new candidate modules, the Aggregate and initial downstream consumers compiled.
- The full run verified 3,762 unchanged dependency contexts and completed **53 of 389** fresh module compilations successfully. The active `WE02JointCreditRankOneRoot` compilation was interrupted for the pause; the remaining 336 modules are not claimed passed. The owned compiler process has ended.
- The source retirement review found 27,080 explicit old internal declarations to retire, preserving the 40 public mass-bound headers, no source references outside the retired scope except those preserved bounds, and no retired source registration commands. This is a source-scope review, not an exhaustive reflection or generated-name proof.

Reproduce the 17 candidate source files without old `/tmp` inputs:

```sh
python3 research/wu-hf4-constructive-wip/producer/produce.py --route constructive --output-dir /tmp/hf4-reproduced
python3 research/wu-hf4-constructive-wip/producer/produce.py --route constructive --output-dir /tmp/hf4-reproduced --check
python3 -m unittest discover -s research/wu-hf4-constructive-wip/producer -p test_portable.py -v
```

The portable producer's nine tests passed, including exact outputs, original headers, mutation rejection and relocated input fencing. The `integration/` scripts and evidence retain historical absolute paths for audit and local resumption; they must be rebound to the local checkout before use elsewhere. The existing 53 successful proof receipts require their actual original objects and exact recursive dependency contexts to be reused; a source list alone cannot establish a resumed proof.

The following procedure described the completed resumption: verify the accepted baseline manifest, keep the old paused run immutable, rebind a new run and reuse only genuinely verified prefix receipts. Finish all 389 affected compilations, compare 696 retained public types and 183 data values (the 40 obsolete compact-model wrappers are explicitly retired), run all 19 planned candidate/final kernel checks, verify final literal statements and standard axioms, reproduce the producer, and only then adopt transactionally and run production checks.

The public census scanned 4,151 modules across 21 scopes and found 2,096 zero-direct-incoming candidates (31,152 provisional lines). It grants no API retirement acceptance and removes no declarations. The separate 22-private-lemma candidate predicts 116 lines; it has not been compiled or installed. The directory's evidence must not be added to accepted savings.
