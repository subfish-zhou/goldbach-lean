# Proof compression candidates

These are isolated experiments, **not installed proof reductions**. The accepted
Wu source manifest and the installed 469,022-line final closure are unchanged.
The accepted baseline remains the [unused-proof audit](../wu-unused-proof-audit/README.md).

The current combined candidate, after the locally compiled max-envelope rewrite,
has a manifest-bound final closure of 3,762 modules and 391,332 effective lines,
77,690 fewer than the installed baseline. The supported whole tree has 431,818
effective lines. See [the current candidate source measurement](combined-max-source-measurement.json).
Its remaining source build and ten-gate validation are still in progress; these
counts are not installed or accepted reductions.


## Shared Pan square-mean estimates

The final theorem uses both `PanV1SquareMean` and `PanV3SquareMean`. Five Type II
helper statements have exactly the types of existing Type I helpers: the
Möbius bound, harmonic sum, multiples count, reciprocal-lcm sum, and divisor
square sum. The candidate adds an acyclic import from Type II to Type I and
replaces their duplicated proofs by applications of those existing theorems.
The original public statements and names remain explicit.

After removing an unused private lcm helper, this candidate saves 445 effective
lines, 460 physical lines and 25,271 bytes. Its module compiles with warnings
treated as errors. All ten public
declaration types match the baseline raw expression trees; all ten axiom
reports in both environments contain only the standard classical axioms.
The old compiled environment confirms the retired private helper was used only
by the replaced Type II lcm proof. Its removal compiles and the ten public types
and axiom checks pass again. Downstream source compilation has now passed;
all 34 subsequent validation gates also passed. Installation remains pending.
See [the record](pan-shared-square.json) and [patch](pan-shared-square.diff).

## Shared singular-series lower bound

The main-term module already imports the finite telescoping product proof of
the same `1/2` lower bound. The candidate reuses that theorem and removes its
duplicate proof and two auxiliary estimates. An actual scan of all 4,151
research modules finds that both helpers are used only by the replaced proof.
The candidate saves 308 effective lines, 323 physical lines and 15,683 bytes.
Its module compiles, all twenty retained public theorem types match exactly,
and both environments' axiom reports contain only the standard classical axioms.
See [the record](shared-singular-series.json) and [patch](shared-singular-series.diff).

## Strict prime cutoff identity

The [Jurkat cutoff patch](jurkat-cutoff.diff) factors four repeated finite-set
arguments through real and natural cutoff lemmas. It saves 21 effective lines,
18 physical lines and 492 bytes. The affected module compiles, and all three
changed public theorem types match their original raw expression trees.
Its reverse import closure contains 1,119 modules. It was included in the
shared-proof batch below to rebuild the combined downstream scope once.

See [the candidate record](jurkat-cutoff.json) and `jurkat-cutoff-evidence/`.
Absolute paths in execution records describe the actual local experiments.

The three candidates together save 774 effective lines, 801 physical lines and
41,446 bytes, before installation. Their combined reverse import closure is
3,297 modules, leaving 854 cache candidates. These foundational dependencies
explain the wider rebuild despite just three changed source files. The
[batch scope](batch-scope.json) records that calculation. `prepare_batch.py`
freezes all sources, checks baseline object and receipt contexts, and retains
only unaffected objects for a subsequent isolated incremental build.

The isolated incremental build at
`/tmp/wu-shared-proof-batch-v1/run-20261028-01` has passed all 4,151 modules,
with an actual terminal exit code of zero and `BUILD_PASS 4151`; see
[the source-build record](batch-build-pass.json). All 34 validation gates have
passed, including the actual `--fresh` replay of the union environment. See
[the validation result](completed-shared-validation.json) and its
[execution archive](completed-shared-validation-evidence-index.json). These
results do not install the candidate savings.
The first invocation compiled
the changed Type II module, then stopped because the cache copy omitted the
Euler–Maclaurin module's auxiliary artifacts. The four missing files were
restored without source changes; `bundle-repair.json` preserves that failure
and the copied hashes. The resumed invocation reused the successful proof
receipt. Source compilation alone is not acceptance, and candidate savings remain
separate from installed measurements.

`audit_completed_batch.py` is a read-only checker for the completed source
build. It requires a terminal successful process and `BUILD_PASS 4151`, then
checks all sources, objects, compiler commands, logs, recursive receipt contexts
and cached auxiliary artifacts. An actual invocation against the running build
correctly refused to write a success result; see `audit-running-rejection.json`.
This checker does not replace interface or kernel validation.

`prepare_validation_inputs.py` has staged 34 subsequent gates outside the
frozen run: before/after exports of 696 retained types, 183 definition values
and 33 public types from the modified modules; exact literal and axiom checks;
old/new retirement controls for three names; twenty-one root-module kernel
replays; compilation of a union root importing those roots; a `--fresh` replay
of that union environment; and both certificate producers. The union's import
closure covers all 4,151 research modules. The staged plan is at
`/tmp/wu-shared-proof-batch-v1/validation-inputs-02/validation-plan.json`.
Actual completed execution is recorded in that directory's `report.json`;
all 34 gates passed. The fresh union replay exited zero after 4,321.86 seconds.
Before and after, all 696 retained raw types, 183 definition values and 33
changed public types matched exactly, and the complete source/object/context
audit returned the same digest. Installation is still pending.

The earlier 32-gate plan omitted `--fresh`: default `leanchecker` replays only
the target module's own declarations, trusting its imports. Its root import
coverage was therefore not complete imported-declaration replay coverage.
Inspection of the pinned toolchain's `LeanChecker.lean` established that
distinction; see [the scope correction](kernel-replay-scope-review.json).
The 32-gate plan was never executed; the 34-gate plan has passed. Historical
execution records remain unchanged, and the historical pruning documentation
now states the narrower scope of its actual root-only commands.

`validate_completed_batch.py` executes those gates only after a terminal
successful build, under the same exclusive Lean lock. Its read-only readiness
check verified ten accepted package revisions and 38 diagnostic input hashes;
an actual invocation correctly refused to start while the build was running.
See `validator-readiness-checks.json`. Neither readiness check executes the
proof-validation gates. That readiness record describes the earlier plan;
the new 34-gate plan's inputs and pinned tools/packages have also been reviewed.

`continue_batch_pipeline.py` observed the completed build and ran that
validator, followed by the compiled proof-family census. Both exited zero.
It did not install changes or restart the source build. The completed
coordinator state is
`/tmp/wu-shared-proof-batch-v1/pipeline-05/process.json`. The first predecessor was
stopped while waiting, before starting a validation child, to add retries for
partially written status files. The source build continued through that
coordinator-only replacement. Four fixture cases check the observation reader; no actual build
status file was modified by those checks.
Coordinator 03 was stopped while waiting, with no validation child, to stage
the additional fresh union replay. Coordinator 04 observed the same source
build and used the new 34-gate plan. No source builder was stopped for this change.

On the later continuation, the old source-build and coordinator 04 processes
and tool sessions were actually missing. Their last status files were not
treated as live handles or successful exits. An exclusive-lock review verified
3,366 completed source/object/recursive receipt contexts, leaving 785 modules.
The same frozen build was resumed with two jobs; all 3,366 completed receipts
remained byte-identical afterward, with zero completed modules recompiled.
See [the resumption record](missing-handle-resume-check.json). Coordinator 05
observed its successful termination and started the unchanged 34-gate plan.
The missing invocation's exit code is unknown; its original records are retained.

After inspecting all 3,297 previous resource logs, the source scheduler was
gracefully checkpointed and resumed with two independent compilation jobs,
each using one Lean thread. The historical maximum per process was 8.19 GiB;
the checkpoint had 25.58 GiB of available memory. The interrupted coordinator
exited with code 130 after its worker finished; this is distinct from a failed
source compilation. All 995 completed fresh-source receipts remained identical
and were reused, with no completed module recompiled. See
`parallel-resume-check.json`; full resource and checkpoint records remain in the
isolated run's `parallel-checkpoint.json`. Sources, their manifest and numerical
precision are unchanged. The exclusive lock still separates build, validation
and census phases; post-build Lean checks remain serial.

## Search evidence

The [compiled type census](type-census/summary.json) scans 57,365 raw theorem
records from the 3,764-module final closure and finds 3,125 type-equality groups.
These groups are search hints. They include generated declarations, original
proofs paired with their own wrappers, and repeated names in raw module records.
They are not counts of removable proofs. A selected replacement must separately
pass import-cycle, retained-interface and compiler checks.

## W10 declaration pilot

The [W10 pilot](w10-pilot.json) addresses repeated interval-expression headers
using a macro that expands to an ordinary opaque theorem. One module compiles,
and all 173 declaration types and declaration kinds match the original raw
records. Its exact text evidence is in `w10-pilot-evidence.tar.gz`, with a SHA-256
inventory in `w10-pilot-evidence-index.json`.

The [candidate producer](../wu2008/diagnostics/w10_bound_declarations.py) prepares
eight modules in a separate directory. Their projected savings exclude the new
macro module and are not accepted measurements. Only the single-module pilot
has been compiled. These modules are outside the final theorem closure, so this
experiment has lower priority than sharing proofs on the final route.

## Further shared proofs

The [Selberg lower-bound patch](selberg-shared-lower-uncompiled.diff) replaces
a repeated Cauchy–Schwarz proof with the existing analytic Selberg theorem.
Both original source headers and proof bodies are identical, and the reused
module is already imported transitively. The isolated patch changes no imports
and projects a saving of 78 effective lines, 89 physical lines and 4,905 bytes.
The isolated source module now compiles, and the changed theorem's raw type
and axiom set match exactly before and after. The first after-export failed
because Lean resolved a namespace root in the candidate library without finding
unchanged sibling modules there. Linking the unchanged baseline artifact bundles
fixed the library layout; only that failed export was retried. The successful
compile was reused. Both attempts and the repair are preserved in the
[mixed review archive](mixed-pruning-review-evidence-index.json).
The shared-proof hunk is included in the mixed pruning batch below. Its full
downstream validation and installation remain pending.

`prepare_generic_square.py` prepares a single character-square estimate for an
arbitrary real coefficient sequence. Both Pan applications retain their exact
source headers and specialize that common theorem. It also removes an unused
local additive-sum witness from the copied common proof. The
[proposed patch](generic-square-uncompiled.diff) replays exactly, and its import
graph is acyclic. Its projected additional saving of 130 effective lines is
relative to the frozen batch, **not an accepted reduction**. Compilation,
retained-type comparison, private-helper use checks and downstream validation
remain pending. The new module is outside the running build.

The [Mertens import candidate](mertens-import-trim-uncompiled.json) replaces the
analytic-number-theory umbrella import with the Mertens theorems and PNT
interfaces that the module explicitly uses. In the static graph, its local
closure decreases from 63 modules to 32, and the reverse closure of a Type II
Pan change decreases from 3,297 modules to 3,042. The final theorem's total
closure remains 3,764 modules. These are graph calculations, not measured build
speed or proof-size savings. Compilation may reveal implicit reexport
dependencies in downstream sources; those must be checked before adoption.

## Further dead-proof search: lexical evidence only

The next [lexical model](next-dead-proofs-summary.json) repeatedly models removal
of proof leaves in memory. It protects the retained interfaces, definition-value
names, current consumers and the seventeen generator-owned Hf4 modules. The
history directory is explicitly excluded from supported builds by the Wu
README; its 1,295 historical Lean files are therefore recorded as archival
inputs rather than current callers. Other exclusions follow the previous audit.

The model reaches a fixed point after 25 nonempty rounds and finds 2,975
candidate declarations in 813 modules. Their **provisional** source spans total
74,042 effective lines. This is not an accepted reduction, an actual compiled
reference count, or a claim that all these declarations can be removed. No
source was edited. The first sixteen rounds agree exactly with an independent
version that rescans the complete source corpus on every round.

`next-dead-proofs-opportunities.json.gz` preserves the full lexical input and
candidate report. `dead_family_census.py prepare` has staged a private-inclusive
compiled census at `/tmp/wu-next-dead-family-census-v1`; its Lean template is
`DeadProofFamilies.lean.in`. It must wait for the current source build and
validation. The census examines references to both named theorems and their
name-prefixed compiler auxiliaries. Its postprocessor retains families with
incoming references from retained declarations, follows that retention through
candidate dependencies, and conservatively retains non-theorem members and
ownership ambiguities. Four synthetic graph cases test that boundary rule;
they are not Lean census results. Compiler source ranges, registrations,
consumers, actual downstream compilation and kernel validation are still
required before deleting any of these candidates.

The [scoped-directive source review](next-dead-scoped-directives.json) verifies
eleven candidate declarations immediately governed by `omit … in` or
`set_option … in`, against the frozen source hashes. If selected for removal,
each needs its governing directive removed with it. This source attachment
check does not supply compiler ranges or authorize deletion.

`prepare_dead_ranges.py` has staged an uncompiled range query for all 2,975
census targets at `/tmp/wu-next-dead-ranges-v1/plan.json`. It reuses the census
resolver and its private-inclusive module coverage checks, then requests Lean's
declaration ranges, name-selection ranges and attached docstrings. Execution
must follow the actual family census and the 34 validation gates. Any later
deletion must match runtime names and exact source ranges, handle governing
directives, and pass downstream compilation and kernel validation.

## Combined proof and definition search: lexical evidence only

The [combined source search](combined-lexical-summary.json) also models unused
`def` and `abbrev` leaves. Searching definitions alone finds 184 candidates with
1,005 provisional effective lines. Modeling proofs and definitions together
reaches a fixed point with 3,807 candidates in 853 modules: 2,987 proofs and
820 definitions or abbreviations, with 78,180 provisional effective lines.
It contains every candidate from the earlier 2,975-proof model and the separate
definition model. Their interaction reveals twelve further proof candidates
and 636 further definition candidates beyond those separate searches.

These are unverified search opportunities, **not deleted or accepted savings**.
The searches changed no Lean source and started no Lean process. Both complete
reports and the exact temporary scanner snapshots are preserved as
`combined-declarations-*.gz` and `unused-definitions-*.gz`, with hashes in the
summary. The existing theorem-only family census and range query cover 2,975
targets; they do not establish the safety of the additional 832 declarations.
An expanded mixed-kind compiled census, source and auxiliary ownership,
registration/consumer review, exact compiler ranges, and downstream validation
are required before any combined deletion. The original frozen build and
running 34-gate validation are unchanged.

## Exact mixed-declaration pruning batch

The combined lexical search was followed by an actual compiled census of all
4,151 research modules, including private declarations and generated auxiliaries.
All 820 definition roots matched their expected source kinds. The compiled
reference boundary selected 2,970 proofs and 745 definitions; 92 other roots
remain conservatively retained.

A separate compiler query returned exact ranges for all 3,807 candidate roots
and metadata for 6,537 family members. `prepare_mixed_deletions.py` checks those
ranges, source names, docstrings, scoped directives, attributes and disjoint
intervals. It then closes retention over both actual compiled dependencies and
source references, including current repository consumers. This catches source
uses erased from the compiled proof term. In this batch, all 3,715 compiled
boundary candidates also passed source closure. No selected name remains in
kept source, and reinserting every deleted fragment recovers the original text
exactly. Eleven scoped prefixes and 2,236 attached docstrings are accounted for.

The isolated overlay removes 76,682 effective lines, 81,400 physical lines and
4,170,123 bytes across 842 modules. Adding the compiled Selberg shared-proof
hunk projects 76,760 effective lines, 81,489 physical lines and 4,175,028 bytes
relative to the already validated shared-proof batch. These are exact candidate
source differences, **not installed savings**. See the
[candidate summary](mixed-pruning-candidate.json),
[review evidence](mixed-pruning-review-evidence-index.json), and
`prepare_pruning_batch.py`.

The frozen new run is `/tmp/wu-mixed-pruning-batch-v1`. It reuses 240 unaffected
module artifact bundles and recompiles the 3,911 affected modules incrementally,
with two independent jobs and one Lean thread per job. Both certificate producer
checks passed against its actual frozen sources before compilation started.
The accepted manifest and installed line counts remain unchanged pending source
compilation, retained-interface/value/precision checks and final kernel review.

`prepare_pruning_validation.py` stages ten final gates at
`/tmp/wu-mixed-pruning-validation-v2/validation-plan.json`. Successful baseline
exports are reused: only the new environment exports are executed for the 696
retained types, 183 definition values, 33 earlier changed types and the additional
Selberg theorem. The literal conclusion and standard axiom checks remain
explicit. The retirement query scans all 4,151 modules, including private data,
for 6,302 original names: all selected declaration families plus the three
previously retired helpers. One union-root compilation and one `--fresh` replay
cover the complete imported environment, followed by both producer checks.

`audit_pruning_batch.py` verifies the full affected dependency closure, every
source/object/log/recursive receipt context and the provenance of the 240 cached
artifact bundles. `validate_pruning_batch.py` requires this audit before and
after its checks. Both tools actually rejected the still-running build without
emitting success output; these readiness rejections do not execute Lean gates.
`continue_pruning_pipeline.py` observes the existing builder's PID/start identity
and starts validation only after a terminal successful result. Its state is at
`/tmp/wu-mixed-pruning-pipeline-v2/process.json`. It never restarts or signals the
source build and never installs changes. Earlier staged plan v1 was not executed;
v2 additionally pins the validation executor and context checker before starting.

A full manifest-bound recount of the frozen candidate (including the earlier
774-line shared-proof batch) is in
[mixed-pruning-source-measurement.json](mixed-pruning-source-measurement.json).
Relative to the installed baseline, its final closure is 391,488 effective lines
and 466,488 physical lines; the whole tree is 432,242 effective lines. Both
scopes remove 77,534 effective lines, 82,290 physical lines and 4,216,474 bytes.
These are actual candidate source counts, not accepted installed measurements.

The accepted baseline has also been preserved before any adoption, with copied
sources, receipts and logs and verified linked artifact bundles; see
[mixed-pruning-baseline-preserved.json](mixed-pruning-baseline-preserved.json).
Its 16,615-entry inventory is compressed separately. A new read of 2,087 current
repository consumers found no selected declaration-name references. The local
`/tmp/wu-mixed-pruning-batch-v1/adoption-plan.json` enumerates the exact source
changes and requires all validation gates before any canonical write. Compiled
artifacts must be installed by atomic replacement to preserve every historical
linked snapshot. The current installed manifest remains unchanged.

`adopt_pruning_batch.py` is prepared for the later installation step; it has not
been executed. It requires terminal source success and all ten actual validation
gates, rechecks every input, consumer and preserved baseline file, and stages only
changed files. It copies changed compiled artifacts independently and atomically
replaces targets. The accepted transaction engine is reused through
`pruning_transaction.py`; rollback links existing artifact bytes, avoiding a
second full artifact copy when disk space is limited. Sources and metadata are
restored as independent copies.

An injected failure after installation in a temporary fixture restored the old
source, artifact and build status, removed a newly created log, preserved the
candidate artifact and left backup source content unchanged after a later edit.
See `pruning-rollback-fixture.json`. An actual preflight against the still-running
source build refused adoption before staging or mutation; see
`pruning-adoption-running-rejection.json`. Neither test installs production code.
After a future installation, four production checks are required: a cache-only
4,151-module build with `--limit 0`, the literal/axiom probe and both producers.
Exact installed source/object/receipt contexts are compared with the validated
candidate; the complete kernel replay is not repeated for identical artifacts.
Acceptance evidence and current documentation are updated only after these pass.

The first mixed-pruning source invocation received SIGTERM after 733 modules
had been reported by the scheduler. The signal's cause is unknown. Its wrapper
returned 1 after recording the terminated builder child's return code of -15;
this is not a reported failed mathematical proof. Both the original process
record and log remain unchanged. Under the exclusive lock, a review verified
928 complete receipts, including unaffected cached modules not yet counted in
the scheduler's prefix, and all source/dependency/object/log contexts. The same
frozen build resumed from these records. All 928 receipts remained byte-identical
after the resumed builder made further progress, with zero completed modules
recompiled; see `mixed-pruning-sigterm-resume.json` and its compressed cache
inventory. Coordinator v1 stopped before starting validation. Coordinator v2
observes the resumed builder and retains the same ten-gate validation plan.

## Retained-root follow-up

[retained-root-auxiliary-review.json](retained-root-auxiliary-review.json) analyzes
the actual compiled census without changing the frozen candidate. The 92
conservatively retained roots receive 138 edges from outside the selected family
map. All 67 direct root references come from the recorded cross-module ownership
issues (equation/congruence auxiliary names). The other 71 edges reference 37
auxiliaries whose actual compiler declaration kind is `theorem`. There are no
direct root edges from other outside users in this census.

These references do not establish that all 92 roots are mathematically needed.
Lean can share a closed proof extracted while compiling an earlier declaration
with later declarations, and can generate equations in a downstream module.
The original census intentionally retains such roots. Before deleting any more,
review equation/matcher ownership, collect incoming references to cross-module
auxiliaries (not present in the current target member map), and compile a local
pilot to test regeneration of shared proofs. Retained types, actual numerical
definitions and downstream checks still apply. No further deletion or source
savings are claimed from this read-only review.

## W08 max-envelope candidate (local compile passed)

[The isolated draft](w08-max-envelope-uncompiled.json) replaces each W08 cell
bound by the maximum of the two already proved bounds for that same E-kernel
integral. Their maximum is still a valid lower bound. Its comparison with the
older bound and the nonnegativity of the increment follow from order alone.
The W17 remainder consumer pays this maximum from the same E-kernel component;
it does not add two credits for that component.

The final 1.8938 theorem uses only these non-strict comparisons. The strict
application is used by an additional frozen-vector consumer outside the final
import closure. That consumer already has a positive zeroth coordinate, so
strictness needs only the nine column-zero comparisons. The candidate removes
72 other entry proofs and moves the remaining strict witness to that consumer.
Its source graph removes `W08Entries0` and `W08EntriesRest` from the final
closure (3,764 → 3,762 modules), leaving no imported entry-comparison table on
that route. The isolated draft projects 156 fewer effective lines in the final
closure and 424 fewer across the whole supported tree. These are candidate
source differences, not accepted savings or a measured compilation speedup.

Underlying grid parameters and rational cell formulas are unchanged. Internal
strict interfaces change to the condition actually used by the fixed vector;
none of the retired names occurs in the retained export requests. The precise
1.8938 conclusion, retained interfaces/data, actual downstream source build and
kernel checks must still pass. See [the patch](w08-max-envelope-uncompiled.diff)
and [uncompiled source evidence](w08-max-envelope-uncompiled-evidence-index.json).
The prototype is in `/tmp/wu-w08-max-envelope-v2`; current frozen sources and
their running build remain unchanged.

The max-envelope prototype has now actually compiled all nine modified modules
against the already validated shared-batch library, including the W17 component
consumer and its diagnostics. All nine original source templates were identical
in that library and the incomplete pruning batch. See
[w08-max-envelope-local-compile.json](w08-max-envelope-local-compile.json) and
[the actual execution archive](w08-max-envelope-local-compile-evidence-index.json).
This remains a local compile result, not full downstream or kernel acceptance.

A deliberate checkpoint preserved 2,178 verified receipts. None of the 309
modules affected by the mathematical rewrite had yet been compiled in this run.
The nine changes were merged into the remaining work, with exactly two import
edges updated. All 2,178 receipts remained byte-identical after compilation
resumed. The previous frozen inputs are preserved at
`/tmp/wu-mixed-pruning-pre-max-inputs-v1`; no canonical source changed.

The active manifest is now
`541e837ffee9ef8ea26be4370323d653b788b518ac3040a3113c8a2aea013ec1`.
Coordinator v3 observes this resumed source build and runs the updated ten-gate
plan at `/tmp/wu-mixed-pruning-validation-v3/validation-plan.json`. The new
retirement census actually found all 84 retired W08 theorem families, adding
them to the previous 6,302 targets for 6,386 absent-name checks. Both previous
pruning validation plans were unexecuted. The final combined cohort retains the
original public type/value, exact literal, axiom and producer checks and performs
one full fresh-union replay. The startup baseline-path audit rejected one
mis-targeted resume attempt before any source compiler was launched; the corrected
wrapper resumed from the same preserved cache.
