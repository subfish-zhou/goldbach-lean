# Wu LiuPan lemma pruning

The accepted Wu proof now uses **533,141 effective lines** in the final theorem's
3,755-module import closure. This phase removes **383 theorem/lemma declarations
from nine LiuPan files**, saving 10,924 effective lines without changing numerical
precision or the public `WuPaper.ClassicalSlots.one8938` conclusion
`r^5000 ≤ q^4469`. The legacy `one894` interface remains.

## Scope and measured reduction

Only declarations without attributes were removed. All retained source fragments,
including definitions, instances, attributes, namespace/section context and surviving
proofs, are character-identical. Original grids, constants, rounding precision and
error budgets are unchanged. The removed interfaces are intentionally retired;
this does not claim that every historical research declaration remains available.

| Scope | Modules before → after | Effective lines before → after | Physical lines before → after | UTF-8 bytes before → after |
|---|---:|---:|---:|---:|
| Complete Wu research tree | 4,142 → 4,142 | 584,819 → 573,895 | 688,537 → 677,021 | 35,406,645 → 34,891,957 |
| `WR2ClassicalCertificate` import closure | 3,755 → 3,755 | 544,065 → 533,141 | 642,059 → 630,543 | 31,197,996 → 30,683,308 |

Both scopes save 10,924 effective lines, 11,516 physical lines and 514,688 bytes.
Against the original 1,126,636-line theorem closure, cumulative savings are
593,495 effective lines. Counts include complete local modules and exclude external
Lake packages; they are not minimal declaration-level proof lengths. Main Chen and
Li–Liu measurements are independent and unchanged by this report.

The [before](../research/wu-liupan-pruning-audit/source-size-before.json) and
[after](../research/wu-liupan-pruning-audit/source-size-after.json) measurements bind
the actual source manifests. The accepted current manifest SHA-256 is
`5edafd3f227eabed812038e21b69b0817577ff459d23c0acc1f89f88953f6cfe`.

## Verification and provenance

The [acceptance record](../research/wu-liupan-pruning-audit/validation.json) binds:

- The complete 4,142-module isolated scope: 3,165 fresh compilations and 977
  independently verified unchanged dependencies.
- Independent literal acceptance, five standard-axiom reports and ten isolated
  kernel replays. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
- Exact artifact adoption, then production `BUILD_PASS 4142` cache/receipt
  verification, production literal acceptance and a fresh final
  `WR2ClassicalCertificate` kernel replay.
- Exact source reconstruction and six mutation negative controls.

The first run reached 2,375 successful modules before `W08EntriesRest` exceeded its
600-second external wait budget. The archived failure remains distinct from the
successful approximately 725-second retry under an 1,800-second wait budget; the
2,375 successful prefix rows were retained. This changed the external wait budget,
not Lean commands, proof budgets or source. No complete historical inherited
`os.environ` attestation is claimed.

The first standalone kernel validation selected a Lean 4.35 `Init` against the
pinned 4.33 checker and failed the object-header compatibility check. That failed
validation is retained. After fixing only the validator's `LEAN_SYSROOT`, all ten
kernel replays passed. Reproduction must set `LEAN_SYSROOT` to the same pinned
compiler prefix as `leanchecker`; the [research README](../research/wu2008/README.md)
contains the command. The source and proof objects were not changed by this fix.

## Portable source audit

From the repository root, the static exact-deletion check can be repeated with:

```sh
python3 research/wu-liupan-pruning-audit/audit.py --repo .
python3 research/wu-liupan-pruning-audit/test_negative_controls.py --repo . --candidate-root research/wu2008/src
```

The [portable audit](../research/wu-liupan-pruning-audit/README.txt) reads original
Git blobs from fixed commit `c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`, verifies all
383 deletion intervals and fragment hashes, and reconstructs both original and
retained text. Its source-level qualified names for private declarations are not
claims about elaborator-generated internal names. Static reconstruction alone does
not prove unusedness or type correctness; the full compilation and kernel checks
above provide the separate mathematical acceptance evidence.

The later 124-definition pruning and structural-sharing candidates are not part
of this accepted phase. Earlier Fifth integer-payment and other compression
reports retain their original historical measurements.

The subsequent [structural compression](WU_STRUCTURAL_COMPRESSION.md) records the current accepted totals; the measurements above describe this earlier phase.
