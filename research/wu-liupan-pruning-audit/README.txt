Portable LiuPan exact-deletion audit (STATIC ONLY)

Required tools: Python 3 standard library and Git, with fixed commit
c4e1b8d00dda9661140f95e0f03f0d5a08d636c2 present in the chosen repo.
No Lean, network, package installation, old Lean snapshots, production imports,
or absolute scratch paths are used by the portable scripts.

Keep audit.py and manifest.json together. Example before adoption:
  python3 audit.py --repo REPO --candidate-root CANDIDATE_DIRECTORY --output report.json
After adoption, omit --candidate-root to audit REPO/research/wu2008/src.
Tests:
  python3 test_negative_controls.py --repo REPO --candidate-root CANDIDATE_DIRECTORY

The manifest binds nine original Git blobs, nine candidate blobs, per-file
physical/effective/UTF-8 counts, and 383 Unicode-character deletion intervals
with exact fragment hashes and namespace-qualified source names. For private
lemmas, these are source-level names, not elaborator-generated internal names.
The embedded nested-comment/string lexer follows the original counting routine.
Exact reconstruction proves all retained text (proofs, statements, contexts)
is character-identical. Each deleted interval contains one theorem/lemma plus
optional comment prefix and no recognized top-level context command.
Expected reductions: 10924 effective lines, 11516 physical lines, 514688 bytes.

Scope: only these nine files. This does not validate dependencies, Lean typing,
axioms or kernel acceptance. It cannot establish that a removed lemma was unused.
Every success explicitly reports status=static_only and lean_acceptance=false.
The manifest itself is a review input, not a signed trust root. Review its hash.

results.json and negative-controls.json record this scratch review. Six negative
controls modify temporary copies only, including a rehashed survivor mutation
that must fail reconstruction independently of the candidate SHA gate.
