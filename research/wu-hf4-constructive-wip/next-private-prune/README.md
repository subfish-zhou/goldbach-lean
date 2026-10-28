# Private proof cleanup candidate — UNCOMPILED

This scratch patch removes22 plain unregistered private theorem/lemma declarations
from13 existing modules in the final theorem's prospective3764-module closure.
The entire4151-source lexical universe was SHA-checked. Each written basename
occurs once in that universe, counting strings conservatively as mentions.
Declaration detection masks strings and handles primed names. Current64 modified
V7 modules are excluded, and no frozen build input or production source is changed.

Root read all22 full declaration fragments and their neighboring declarations.
The patch removes the two docstrings attached to removed lemmas and preserves
every following declaration's docstring. Exact character intervals and fragments
are in manifest.json. Inserting the deleted fragments back at original offsets
restores every original byte. All retained source characters are unchanged.

`python3 prepare.py` reproduces13 overlay files, candidate.diff and manifest.json,
rechecking all audit source bindings. Source measurement predicts116 effective
lines,119 physical lines and5230 UTF-8 bytes removed. No definitions, numerical
fields, constants, public statements, instances or registration commands are
changed by these intervals.

This is not Lean acceptance. Unannotated private theorems can still participate
in tactic library search without an explicit name token. The13 files and their
downstream dependents must be actually compiled, with retained interfaces and
relevant literal/axiom/kernel gates checked. Exact source offsets should be
rebound to the genuinely accepted baseline before any later adoption. Prefer
combining this small cleanup with the next Hf4 integration build; do not interrupt
the active V7 build or modify its pinned serial post-build pipeline.
