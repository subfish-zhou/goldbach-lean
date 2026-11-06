# Accepted Hf4 constructive compression

The installed 1+1.8938 proof preserves its original precision, grids, error budgets, 40 mass-bound statements and 80 endpoint targets. This phase saves **25,298 effective Lean lines**, **38,556 physical lines** and **2,759,754 bytes** in both measured scopes, including all added proof modules. Full inventory: **4,151 modules / 540,985 effective lines**. Final theorem import closure: **3,764 modules / 500,231 effective lines**.

See [validation.json](validation.json), [measurement.json](measurement.json), [actual isolated acceptance](isolated-acceptance.json), [actual production verification](production-verification.json) and the [mathematical explanation](../../docs/WU_HF4_CONSTRUCTIVE.md). These count complete local modules, not a minimal declaration-level proof; external Lake dependencies, historical copies and generator templates are outside that module-source metric.

The full source scope verifies 3,762 unchanged dependency contexts and 389 actual source-proof receipts: 53 genuinely verified proofs from the paused run and 336 subsequent compilations. The raw resumed runner's legacy `fresh_compilations` field counts all 389 proof rows; it does not mean 389 new executions. All 25 isolated acceptance gates passed: 696 retained public types, 183 raw definition expressions, final literal statements and standard axioms, 19 fresh candidate/final kernel replays, generator reproduction, and identical complete before/after source contexts. The 40 old internal compact-model wrappers are explicitly retired; their 40 original mass-bound interfaces are preserved.

The transaction `../wu2008/build/adoptions/hf4-constructive-v1-1793187552084001964` stages 881 exact targets with rollback backups. After installation it passed generator reproduction, the 4,151-module recursive receipt check, final literal/axiom checks and a fresh production final-module kernel replay. Its raw source proof receipts, commands, sources, logs, original prefix receipts, all validation evidence and tool sources remain archived there. [Export review](export-root-review.json) independently reconstructs the exact exporter programs and checks requested names, payloads, strict commands and sole local libraries; [toolchain review](toolchain-review.json) matches compiler/checker/Init hashes and all ten package revisions with the accepted baseline.

Reproduce the current source generator and measurement:

```sh
python3 research/wu2008/diagnostics/hf4_constructive/produce.py --route constructive --output-dir research/wu2008/src --check
python3 research/wu-hf4-constructive-audit/measure.py
```

The old `hf4_compact_certificates.py` CLI now delegates to the constructive producer by default; `--panel` retains the historical standalone probe. The exact old arithmetic reference survives once in the new producer's frozen `lib/legacy_hf4.py`.

The [pause/resume snapshot](../wu-hf4-constructive-wip/README.md) remains historical evidence. Its separate public/private pruning candidates are still unaccepted and excluded from these savings; their old census must be rebound to the new installed contexts before further retirement.

后续已采用的[未使用证明剪枝](../../docs/WU_UNUSED_PROOF_PRUNING.md)另减少 31,209 行有效代码。本文及本阶段验收 JSON 保留为 Hf4 历史快照；当前统计以该后续阶段为准。
