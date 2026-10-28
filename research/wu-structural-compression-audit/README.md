# Wu structural compression acceptance

The installed 1+1.8938 tree preserves the original grids, numerical precision, error budgets and literal bound `r ^ 5000 ≤ q ^ 4469`. This phase saves **7,612 effective lines**, **9,092 physical lines** and **467,539 bytes**, including all added modules. The full tree has 4,151 modules / 566,283 effective lines; the final theorem import closure has 3,764 modules / 525,529 effective lines.

See [validation.json](validation.json), [measurement.json](measurement.json), [actual production verification](production-verification.json) and [phase explanation](../../docs/WU_STRUCTURAL_COMPRESSION.md). Effective lines use the published `scripts/check.py` lexical counter with strings retained. External Lake dependencies are excluded.

The local adoption archive is `../wu2008/build/adoptions/structural-v9-1793177513339524821`: it preserves source-proof receipts, 78 acceptance gates, registration/private-scope reviews, generator reproduction, failed runs, bounded proof-parameter bridges and the 4,709 historical orphan receipts. Removing receipt metadata is not counted as Lean code savings. Production verification reuses 3,500 actual source compilations and verifies 651 unchanged dependencies; its cached check is not represented as 4,151 fresh compilations.

The private-inclusive constant census covers 4,151 modules in 21 scopes. All 2,096 candidates have zero direct incoming references. This is research-scope metadata, not proof of external API or registration safety; none of its provisional 31,152 lines has been removed. The separate uniform Hf4 semantic prototype also remains uninstalled.
