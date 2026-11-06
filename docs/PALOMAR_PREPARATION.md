# Palomar preparation and code-quality work

## Submission scope

The preparation covers the complete Chen and Li–Liu main libraries and the
independent statements in `Palomar.Challenge`. The comparison selects Chen's
qualitative theorem and Li–Liu's natural-power and real-power existence theorems.
The quantitative main-library endpoints have their own literal statement and
axiom checks.

The working repository also contains an independently pinned Wu research project
and content-addressed historical sources. The publication exporter includes the
complete upgraded main proof development, its independent statement and solution,
and the pinned build environment. Run the exporter from the working repository.

```sh
python3 scripts/prepare_palomar.py --output .build/palomar-next --author "Ziyu Zhou"
python3 scripts/check_palomar_sources.py .build/palomar-next
```

Choose a new output directory for each export. The copied sources are hashed in
`Palomar/source-manifest.json` inside that directory. The confirmed author and maintainer is
Ziyu Zhou, with [ORCID 0009-0009-7661-7545](https://orcid.org/0009-0009-7661-7545).
The historical AI-assistance and inherited-source credit records in
`formalization.yaml` require maintainer review. The research sources
retain their original bytes and their separate verification records.

## Pinned environment

| Component | Selected version or revision |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| LeanArchitect | `9f3bb53916b9d6fa05b7777389e1844f82b1c9a6` |
| doc-gen4 | `0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae` |

The selected stable release satisfies Palomar's checked minimum of
`v4.35.0-rc2`. Dependencies are fixed by the Lake configuration and manifest.

The initial module port uses public imports and exposed public sections to
preserve the existing downstream interface and definitional reductions. Private
helpers used by exposed definitions or public statement types receive explicit
visibility where required by Lean. Import and transparency minimization require
subsequent review of individual modules.

## Verification sequence

1. Build all four main libraries with warnings treated as failures.
2. Run the existing literal-statement and standard-axiom checks for all six
   protected public endpoints.
3. Recheck the internal strengthened statements and run the script tests.
4. Replay the public theorem and check modules with `leanchecker`.
5. Rebuild and inspect the declaration inventory and the Blueprint.
6. Compile `Palomar.Solution` and compare it with the independent Challenge.
7. Inspect the complete publication bundle against Palomar's source requirements.

The Challenge carries deliberate specification holes. Comparator must establish
the corresponding Solution proofs using only `propext`, `Classical.choice` and
`Quot.sound`. Its imports resolve through the pinned Mathlib environment.

The final producer guard loads the complete stored proof environment at private
olean level, with extension loading disabled. This gives its existing traversal
access to theorem bodies hidden by ordinary module imports. Its original
producer list and forbidden-trust checks are retained. The optional proofopt
commands receive the same module-boundary handling, while retaining support for
local declarations in the current file.

## Completed main-library checks

The warning-free main build covers 1,803 modules and 10,863 jobs. All six public
literal-statement and axiom probes, the unchanged strengthened-statement probe,
five named kernel replays and the compiled Palomar Solution pass. The script
suite has 123 passes and one optional fixture skip. The proofopt Python suite
has 32 passes, and its Lean fixture runner covers the module-import proof-body
regression.

The complete declaration census retains the six protected endpoint kinds and
type hashes. The [interface inventory](../Palomar/interface-review.json) lists
66 added names and 731 cross-version raw type-hash changes. It identifies the
removed compiler-generated constructor-index helper explicitly. The
[source comparison](../Palomar/source-fidelity.json) records the protected source
bodies and the producer guard's original target list.

Fresh local Blueprint extraction and rendering pass with 68 nodes, 120 edges,
four chapters and six exits. The pinned documentation driver builds and passes
normal four-module API generation. The [validation record](../Palomar/validation.json)
contains the commands, source pins and additional publication results.

## Independent replay and NanoDa repair

The verified publication is `.build/palomar-verified`. It contains all 1,803 main
proof modules and two Palomar modules, with a maximum of 5,962 physical lines
per source. Its warning-free default build, six public endpoint checks,
50 script tests and whole-publication source-format checks pass. The publication
exporter reproduces all 1,816 copied input hashes after the documentation refresh.

The local replay uses the unmodified PalomarSubmission verifier at
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. Its positive and negative
Comparator controls pass. The verifier checks dependency provenance, compiles
the Challenge separately against allowlisted dependencies under a fresh protected
alias, exports both modules and runs the protected judge with the original
bundled Lean and NanoDa binaries. Both mandatory checkers accept the complete
Solution export. The registry-pinned con-ron passes its matching and ill-typed
controls and accepts the export with two workers. The additional bundled
Lean paranoid, lean4lean and con-leche checkers also accept it.

The first failing auxiliary declaration was the closed coefficient identity in
`goldbachPositiveScalarA_hasDerivAt`. Four similar certificates in
`LiLiuGoldbachS3IntegralScalarCoefficients` also exhibit excessive reduction
cost under the bundled NanoDa. The repair introduces the proved lemma
`S3Polynomial.eq_of_num_den_eq`. Each certificate decides equality of the
numerator/denominator pairs, then applies rational and list injectivity.

The repair changes three proof files and adds 19 physical lines. The declaration
inventory gains one shared lemma. Exactly five private arithmetic-certificate
types change to pair-list equalities. All other existing declaration types,
including the six protected public endpoint hashes, match the preceding accepted
Lean 4.35 snapshot. The numerical literal sequences in the three edited files
match that snapshot. The full producer-reachability guard also passes.

The [NanoDa verification record](../Palomar/nanoda-verification.json) records
checker hashes, isolated reproductions, the complete successful replay and its
measured memory. The [proof-term profile](../Palomar/proof-term-profile.json)
records the final export. Earlier stack and increased-memory failures are kept
as historical diagnostics in the [validation record](../Palomar/validation.json).

Local builds reuse verified caches. The replay uses the pinned bubblewrap 0.12.0
and Palomar's cgroup supervision. The hosted-provider capacity preflight,
publication commit and registry registration belong to the submission workflow.
The historical automation account and source relationships still require the
maintainer's review.
[Palomar verification policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

## Quality improvements in this port

The compatibility work makes direct imports explicit when Mathlib changes its
public import surface. It updates deprecated ordered-product and conditional
APIs, replaces obsolete tactic syntax and removes tactics identified as unused
by the current compiler. The elementary and polynomial derivative elaborators
receive explicit metaprogramming stages.

The additive-combination tactic retains its equality-expression grammar from
the earlier Mathlib dependency, including the original attribution. This keeps
its additive-group behavior available during the upgrade. Reviewing this legacy
parser against the modern tactic API is a separate maintenance item.

## Subsequent quality work

| Priority | Area | Concrete work |
|---|---|---|
| Before registration | Publication metadata | Review the historical automation account and source relationships, then select the public publication commit |
| High | Public interfaces | Review the exported helper names and the imports each public statement needs |
| High | Proof readability | Add short mathematical explanations to long analytic proof blocks |
| Medium | Module structure | Split large files along mathematical responsibilities and verify the resulting import graph |
| Medium | Generic analysis | Review rational-power conversion, moving-region integration and finite-cover integral estimates against current Mathlib APIs |
| Medium | Numerical certificates | Document the relation between certificate data, checked inequalities and consuming declarations |
| Ongoing | Upstream contributions | Prepare small independent Mathlib contributions after API review and human proof review |

The generic-analysis candidates are implemented in `MathlibNt.Analysis.RationalPower`,
`MathlibNt.Analysis.MovingIntervalIntegral` and
`MathlibNt.Analysis.IntegralExcessCover`. Their upstream preparation includes
checking current declarations and open pull requests, choosing the appropriate
generality and namespace, and validating the normal library entry points.

## Concrete review targets

The main library has three files over 3,000 physical lines. The largest is
`MathlibNt/SieveTheory/JurkatRichert1965ChenGammaOneQOne.lean` at 5,962 lines,
followed by `PrimeNumberTheoremAnd/MediumPNT.lean` at 3,884 and
`PrimeNumberTheoremAnd/ZetaBounds.lean` at 3,581. A split needs a reviewed
mathematical boundary and a new complete build and interface check.

Public visibility review starts with the helpers promoted to support exposed
constructions and statement types, including `eq19SharpRealPackage`,
`exists_primeError_start`, `dvd_of_radical_eq`, `logScaleDeriv` and the
`ProductionDyadicConductor` auxiliary namespace. The original downstream
interfaces are the compatibility contract for that review.

The documentation project is pinned to the same Lean release and a compatible
doc-gen4 revision. Its `GoldbachDocs.lean` driver keeps the legacy format required
by that dependency. The independent publication includes the main proof sources
and Palomar entry points. The full documentation builder remains in this working
repository.

The module and source-size requirements are checked against the
[Palomar contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
