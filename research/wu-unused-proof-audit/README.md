# Accepted unused-proof pruning

This audit records 2,119 retired proof declarations in 1,082 Wu modules.
The installed tree saves 31,209 effective lines and retains the exact 1.8938
endpoint, numerical definitions, precision, grids and error budgets.

See [the report](../../docs/WU_UNUSED_PROOF_PRUNING.md),
[measurements](measurement.json), [acceptance](validation.json),
[isolated gates](isolated/report.json), and [production checks](production-verification.json).

`historical-evidence.tar.gz` stores actual text evidence, original source proof
receipts, and the frozen baseline text consumers. Its exact inventory and hashes
are in `historical-evidence-index.json`. It excludes compiled binary artifacts.
Absolute paths in historical commands describe the original execution only.
`retired-declarations.json` contains exact deleted fragments and compiler ranges.
Remaining development-comment mentions resolve through that index; see
`comment-reference-review.json` for the explicit limits of the comment review.

Run `python3 research/wu-unused-proof-audit/verify.py` from the repository root
to check stored evidence and current source measurements. This does not rerun Lean.
Historical phase audit JSON files are preserved unchanged.
