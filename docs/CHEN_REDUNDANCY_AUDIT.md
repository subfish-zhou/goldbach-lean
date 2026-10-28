# Chen 1+2 redundancy audit

This page records the first accepted structural cleanup. The subsequent
[comparison with the five supplied full texts](CHEN_PAPER_COMPARISON.md)
consolidates the finite Selberg optimization proofs further. Source sizes and
validation fingerprints below refer to their original snapshot.

## Applied cleanup (2026-10-25)

The authorized cleanup has now removed 392 old modules and added one small
primitive square-mean module. The full main tree falls from 350,143 to 234,557
effective code lines: **115,586 lines removed net**, including moved code.
Chen's import closure falls from 216,923 to 99,787 effective lines; Li–Liu's
falls from 331,316 to 220,347. The standalone Wu sources are unchanged.
See the [complete size comparison](SOURCE_SIZE.md) and its
[machine-readable measurements](../research/chen-audit/source-size-after-cleanup.json).

Changes include:

- Extract the fixed complex primitive square-mean estimate from the obsolete
  Chen moment/contour branch. Retain its actual large-sieve proof.
- Delete unused q¹ diagnostics, level-supported and boundary/mesh switching
  interfaces, historical conditional exits, and empty compatibility reexports.
- Remove unused declarations inside retained modules and 1,276 transitively
  implied direct imports. Preserve source elaboration requirements, such as
  local notation and simplification rules, as well as compiled references.
- Derive Chen existence from the actual `0.67` representation lower bound;
  remove the separate existence assembly and unused eight-field certificate.
- Share the unconditional Siegel–Walfisz/Bombieri–Vinogradov producer between
  base and switched-source consumers. Reuse Mathlib's Moebius divisor identity.
- Narrow the adapted PNT import to `MediumPNT`, remove the alternate Wiener
  component, and keep the elementary logarithmic estimate at its lower source.

The scan preserves uses from all main modules outside the original Chen import
closure and the public Chen endpoints. It also keeps the selected mathematical
Blueprint declarations. This removes confirmed redundancy within that scope;
it is not a claim that the proof is mathematically minimal. Internal historical
module paths and unused declarations are intentionally removed.

The noncoprime correction, repeated-prime accounting, uniform medium-prime
estimates, actual counting carrier and the quantitative `0.67` margin remain.
Original author and license notices are retained in surviving files. Old cached
objects for deleted modules were moved outside the active import path before
validation. No build-time improvement is inferred from source-line reductions.

The type census utility is [TypeCensus.lean](../research/chen-audit/TypeCensus.lean).
It reads a tab-separated manifest of source path, compiled object path and
output JSON path. In each matching built checkout, run:

```sh
lake env lean --run research/chen-audit/TypeCensus.lean manifest.tsv
```

The comparison erases binder names and metadata, retains universe parameter
names, and excludes private and obvious generated names. Type hashes are an
additional regression check; the literal endpoint probes and kernel replays
supply the mathematical acceptance gates.

### Retained modules outside Chen's stored-reference closure

The post-cleanup import census distinguishes stored proof references from source
elaboration and other supported consumers. After removing the final empty
`SuzukiProposition118InitialStripReduction` module and its compatibility entry,
the remaining categories are:

| Modules | Reason retained |
|---|---|
| `AnalyticNumberTheory`, `SwitchingPrinciple` | Documented public library import interfaces |
| `Sieve.BombieriVinogradov`, `Sieve.PanMeanValueBody`, `Sieve.SelbergIdentities` | Actual references from other main-library consumers, including Li–Liu's prime/AP counts and source estimates |
| `LargeSieve.LcmWeightBounds`, `LargeSieve.LiLiuPrereqFouvryDivisorMean`, `Switching.BoundaryDensity` | Actual references from Li–Liu divisor/weight bounds and Rosser-factor consumers |
| `Tactic.ElementaryDeriv`, `PrimeNumberTheoremAnd.Sobolev`, `PrimeNumberTheoremAnd.Tactic.AdditiveCombination` | Proof elaboration support, including tactic registrations and definitional simplification; Sobolev declarations also have stored references from the retained Fourier module |

The [retained-module evidence](../research/chen-audit/retained-import-only-modules.json)
lists incoming references from the complete current main-library census.
These are not another deletion budget. Importing the elementary logarithm
module directly in `ChebyshevTheta` also deliberately records the source of the
estimate used there, even though that import is transitively available.

Lean realizes one generated equation theorem, `suzukiActualT.eq_def`, in more
than one consumer with different private match-splitter proofs. The census
records these variants and conservatively unions their stored value references.
Their type references agree. Conflicting ordinary declarations still fail the
census rather than being silently merged.

Acceptance passes the full 2,142-module warning-free build, both endpoint
literal/axiom probes, five public-module kernel replays and 115 script tests
(one optional full-export test skipped). The structural type comparison finds zero changes
among 5,302 surviving public declarations in the original Chen closure.
Wu source/history hashes and existing source-bound receipt checks pass again.
The [validation record](../research/chen-audit/validation.json) and
[post-cleanup census](../research/chen-audit/analysis-after-cleanup.json) retain
source and object fingerprints. The [verification guide](VERIFICATION.md)
separates these checks from historical full Wu acceptance.

The Blueprint catalogue retains 68 mathematical nodes and all six expected
exits. Its 125 rendered dependency edges and four chapter graphs pass
reachability and source-link checks; 67 source positions are refreshed from
actual exported declaration locations.

The original observations below are retained as dated before/after context.


The original audit below, dated 2026-10-25, examines revision
`c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`.
It finds substantial import and historical-interface overhead, together with
several concrete opportunities to share proofs. At the time of that initial audit, no production Lean source had been
changed. The measured candidate size is not a verified deletion budget or a
build-time benchmark.

The [machine-readable evidence](../research/chen-audit/analysis.json) contains
the complete module inventory, source/object fingerprints, unused-module list,
type-match candidates and modeled declaration-graph changes. Reproduce the current core measurements after building the main libraries:

```sh
python3 research/chen-audit/reproduce.py --output /tmp/chen-audit-new
```

The three isolated compilation experiments are historical: use the matching
pre-cleanup `c4e1b8d0` sources with this audit tool and add `--experiments`.
They refer to modules removed by the cleanup and cannot run on the new tree.

The output directory must be new. The audit reads the existing compiled objects;
it does not rebuild project modules. A fresh source build is therefore a
prerequisite. Raw extraction and experiment logs are written only to that output
directory.

## Original audit: mathematical route and literature coverage

The switched upper-bound route follows Zihao Liu's
[2022 corrected proof](https://arxiv.org/html/2203.07871v1). The formal project
also constructs the lower sieve and analytic inputs which the short article
treats as prior results. This is a completed development with replacement proofs
at some input boundaries, rather than a line-by-line transcription of one paper.

| Mathematical input or step | Current implementation |
|---|---|
| Finite representation and multiplicity accounting | `Switching/Weights`, `Switching/CorrectedSievePanBridge`, `Switching/WeightedCounting` and their consumers |
| Weighted lower sieve | `JurkatRichert1965ChenRichertConsumer`, constructed delay functions and Suzuki comparisons |
| Ordinary prime distribution | `Bombieri1965Richert418Unconditional`, using a modern large-sieve/Vaughan/Siegel producer |
| Coprime switched-source distribution | `LiuPanUnweightedUnconditional` and `ChenLiuCoprimeProducer*` |
| Selberg optimizer and noncoprime error payment | `Selberg/Liu/*`, including the actual source and its aggregate error |
| Source-to-corrected triple transport | `LiuSelbergCorrectedChenBridge` |
| Representation lower bound and existence | `ChenVerifiedPrerequisites`, `ChensTheoremUnconditional`, `Goldbach.Theorem` |

The historical density construction and the actual Goldbach density must be
distinguished. The [consumer's source documentation](../MathlibNt/SieveTheory/LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean)
explicitly uses modern Suzuki comparisons for the latter. Its supporting
[Rosser–Iwaniec notes](https://www.suzuyu1729.com/notes/NagoyaSeminar2022/RosserIwaniec.pdf)
are by Yuta Suzuki, dated March 14, 2023; the relevant comparison and uniformity
steps are in Sections 13–14. The lower and varying-prime upper inputs cannot
simply be removed on the grounds that the main article is short.

All thirteen references in Liu's bibliography were classified for their role:

| Liu reference | Role in the comparison | Access checked in this audit |
|---|---|---|
| [1] Bombieri 1965 | Distribution input; implemented with a modern replacement proof | [Publisher record](https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/S0025579300005313); original full proof not reviewed |
| [2] Chen 1973 | Lower-sieve route, numerical target and primitive large sieve; much of the original Lemma 6 chain is outside the endpoint reference closure | Bibliography and source-module correspondence; full original article not obtained |
| [3] Davenport 1980 | General analytic background | Bibliographic classification; textbook not reviewed in full |
| [4] Estermann 1932 | Historical earlier almost-prime result | Historical-context classification, not an additional endpoint premise |
| [5] Jurkat–Richert 1965 | Delay-function/sieve source, with the actual-density distinction above | [Publisher record](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/11/2/95841/an-improvement-of-selberg-s-sieve-method-i); full-text download returned HTTP 403 |
| [6] Kuhn 1954 | Historical weighted-sieve background | Historical-context classification |
| [7] Pan–Wang–Ding 1975 | Switched-source distribution input | Bibliography and [author bibliography](https://amss.cas.cn/ryszl/dxq/lwzz/); original full article not obtained |
| [8] Richert 1969 | Weighted finite-chain source and distribution normalization | [Publisher record](https://www.cambridge.org/core/journals/mathematika/article/abs/selbergs-sieve-with-weights/045BB37A164D6FF9F44469FD8742D824); original full proof not reviewed |
| [9] Selberg 1947 | Upper-sieve method; optimizer is proved in the implementation | Bibliographic and source-level comparison; original article not reviewed in full |
| [10] Vinogradov 1965 | Alternate historical source of the distribution theorem | No separate Vinogradov proof is needed merely because the theorem has two names |
| [11] Wang 1956 | Historical earlier conditional result | Historical-context classification |
| [12] Wang 1962 | The main article's optimizer reference, as well as historical context | Bibliographic/source-level mapping; original full article not obtained |
| [13] Wang, edited volume 2002 | Historical and sieve background | Bibliographic classification; volume not reviewed in full |

This is not a claim that every cited original or every recursively cited book
has been read in full. The main article and relevant Suzuki statements were
available; several original sources were not. That limits literature-level
claims of mathematical redundancy, while the compiled-reference and isolated
compilation findings below do not depend on access to those missing originals.
Other reused foundations, including the adapted PNT proof, are attributed in
[PROVENANCE.md](PROVENANCE.md).

## Import size versus actual stored references

The audit reads every compiled `ConstantInfo` in the 743-module local import
closure of `Goldbach.Theorem`, including private object parts. It follows
references in declaration types, proof/definition values and recursor rules.
External dependencies are leaves. All reached local references have local
providers in this census: there are no unresolved local references.

| Scope | Local modules containing reached declarations | Effective lines in those complete modules |
|---|---:|---:|
| Public module's complete import closure | 743 | 216,923 |
| Existence endpoint only | 522 | 145,726 |
| Public `0.67` count endpoint only | 519 | 144,411 |
| Union of both endpoint reference closures | 524 | 145,787 |
| Imported modules with no reached declarations | 219 | 71,136 |

The last row accounts for 32.79% of the import-closure code lines. It is an
investigation set, not 71,136 lines already removed. The 145,787 figure still
counts entire modules, including unused sibling declarations. Conversely,
notation, instances, attributes and tactic elaboration can require imports even
when their providers leave no reference in a stored proof. Recompilation is
required before an import deletion is accepted.

The census has 19,800 distinct local declarations; 7,244 are reached by the
union of the two endpoints. This count includes compiler-generated declarations
and must not be presented as a count of handwritten lemmas.

## Findings and concrete treatments

### 1. A basic large-sieve tool imports a long original-Chen chain

[`ChenLiuCoprimeProducerShort`](../MathlibNt/AnalyticNumberTheory/LargeSieve/ChenLiuCoprimeProducerShort.lean)
imports `Chen1973Lemma6Equation19UniformMoments` for a fixed primitive large-sieve
constant, its positivity and the complex-coefficient estimate. Those tools are
located near the beginning of a module which imports `Equation19MomentTransport`.
The remaining original-Chen moment and contour material is consequently imported
with them.

Within the imported `Chen1973` directory, 62 of 66 modules supply no reached
declarations; those 62 modules contain 18,422 effective lines. The four reached
modules include the primitive large sieve, which is necessary for the present
Pan producer. Removing all Chen-named material would therefore be incorrect.

**Verified isolation:** the initial fixed-constant and complex-estimate segment
compiles with `-DwarningAsError=true` after replacing its heavy import with the
direct `Chen1973Lemma2PrimitiveLargeSieve` import. This demonstrates a working
lower-level home for the basic tools. It does not establish that this single
change removes all 62 modules: other import paths must also be separated.

**Treatment:** move the fixed primitive estimate into a small shared module,
make both consumers import it, and retain original Lemma 6 material as a separate
source route.

### 2. Diagnostic q¹ and old Abel routes accompany the production triple bridge

[`LiuSelbergCorrectedChenBridge`](../MathlibNt/SieveTheory/Selberg/Liu/LiuSelbergCorrectedChenBridge.lean)
mixes the production triple estimate with stronger-hypothesis wrappers and later
diagnostic q¹ assemblies. Its two imported `LevelSupported` modules have no
reached declarations and contain 2,921 effective lines. Six imported `LiuPan`
modules have no reached declarations, totaling 4,914 lines; the set includes
old Abel and dyadic-aggregate modules.

**Verified isolation:** the source prefix through
`liu_pan_wang_ding_strictTriple_upper` compiles after removing the direct
`Q1LevelSupportedSieve` and `LiuPanCombinedAbelDeterministic` imports. The same
mathematical upper-bound interface is retained. This tests that prefix, not every
historical consumer or a completely rewritten project.

**Treatment:** give the production triple bridge its own module; retain old
diagnostic interfaces behind an explicit compatibility import. Several affected
modules have other import paths, so these candidate sizes are not additive savings.

### 3. The switching facade pulls historical numerical and boundary routes

`SwitchingPrinciple` imports `Switching.EndpointAssembly`, which in turn imports
a long sequential chain. Ten imported `Switching` modules have no reached
declarations, totaling 13,859 effective lines. They include earlier mesh,
boundary, screened-residual and integral-comparison machinery.

`EndpointAssembly` contains 89 compiled declarations, of which only three,
including generated helpers, are reached. Its production existence consumer is
near the end of a file that also retains historical counting contracts and
coarse-error routes. These observations concern the two final endpoints; they
do not say the historical theorems are false or unused by every library user.

**Treatment:** separate the actual finite counting and production endpoint
modules from the historical facade. Checking only whether a direct import is
already transitively available is insufficient: 316 such direct import edges
were found, but deleting an implied edge alone usually leaves the same closure.

### 4. Existence separately repeats an endgame already supplied by the count

The count endpoint proves a positive `0.67` main-term lower bound for the actual
good-representation set. The existence endpoint instead runs a separate
weighted-lower/triple-upper positivity assembly with its own error choice.

**Verified implication:**
[`ExistenceFromCount.lean`](../research/chen-audit/ExistenceFromCount.lean)
proves the exact public `Goldbach.ChenTheorem` directly from
`Goldbach.representation_lower_bound`. It passes with only `propext`,
`Classical.choice` and `Quot.sound`. The test imports the existing facade to
establish the implication; it is not a claim that imports have already shrunk.

**Treatment:** expose a count-to-existence helper below the public facade and
use it for the existence endpoint. Preserve the quantitative theorem and its
coefficient. Remove the duplicated eventual-error endgame from the production
path when compatibility permits.

### 5. A proof certificate is constructed to project a single field

`ChenVerifiedPrerequisites.chens_theorem_of_liu_coprime` uses
`chenFacingSourceChainCertificate.weightedLowerBound`. That certificate packages
eight proved fields. Its proof value refers to the finite Richert source chain
and explanatory identities, although this use only needs the weighted lower
bound, which already has a direct theorem `chenWeightedLowerBound`.

Replacing the certificate reference with the direct bound in a declaration-graph
model removes 34 reached declarations; two module providers containing 210
effective lines cease to be reached. These are modeled reference changes, not
an executed deletion or a minimal proof-size claim.

**Treatment:** use the direct bound at this consumer. Keep the larger certificate
for source correspondence and explicit inspection.

### 6. Two unconditional producer families provide the same analytic contracts

The `Bombieri1965Richert418` and `fourFactor_*` families each supply the raw
Landau–Siegel interface, a nonprincipal primitive Siegel–Walfisz input and
Standard BV. The final Chen route uses both families through different consumers.
The lower-level builders are partly shared, so this is not two entirely
independent copies of every analytic proof.

Modeling all references to the four-factor raw provider as references to the
Richert raw provider leaves six module providers, containing 796 effective
lines, outside the endpoint reference closure. The opposite replacement leaves
three providers containing 283 lines outside it. These are non-additive graph
models and do not measure elaboration time or prove a preferred provider is
globally optimal.

**Treatment:** select one unconditional provider for each common production
contract. Preserve alternate proofs behind separate imports when useful, and
check dependency direction and all consumers before changing the facade.

### 7. An unused alternate PNT component accompanies required PNT inputs

`PrimeNumberTheoremAnd.Wiener` supplies no reached declaration in this census
and contains 3,274 effective lines. Four other small PNT-tree modules also have
no reached declarations. The actual PNT and Mertens inputs remain necessary.

**Treatment:** narrow the adapted PNT import route after checking its import
effects. Do not substitute an unproved PNT interface or delete the analytic
distribution foundations merely because the final theorem mentions only primes.

### 8. Matching theorem types mostly already share their proofs

A supplementary type census erases binder names and metadata and hashes the
resulting types. It finds 82 candidate groups containing 174 public,
nongenerated theorem declarations. Hash matches need checking and do not imply
equal roles or duplicate proof bodies. Of the 82 groups, 67 already contain a
direct reference to a same-group theorem; these are evidence of existing reuse.
The remaining 15 groups include trivial repeated facts, unused old interfaces,
the producer families above and a few independently written small proofs.

For example, the quadratic L-value norm/real-part identity appears in both
`Bombieri1965Theorem4LogInduction` and `Bombieri1965Theorem4TwoCharacterValueUpperBound`.
The real Moebius divisor-sum identity appears in both `VaughanIdentity` and
`SelbergUpperBound`. A shared provider or an existing Mathlib result can replace
these repetitions without importing an entire higher-level consumer.

**Treatment:** consolidate the genuinely separate small proofs, retaining
public aliases where needed. Do not report all 174 declarations as duplicated
work or all 82 groups as new simplification opportunities.

## Material which should not be deleted as redundancy

- The noncoprime switched-source correction: it pays the error not covered by
  the coprime distribution contract. Its necessity is the subject of Liu's
  corrected proof, Section IV.
- Valuation and repeated-factor accounting: the public target allows prime
  squares, and the corrected finite weight must control multiplicities.
- Source/corrected-carrier transport, including integer cutoffs and exceptional
  residual primes: the counting objects really have different boundaries.
- Uniformity across the varying medium-prime family: a pointwise eventual
  statement does not provide one threshold for the whole family.
- The genuine logarithmic-integral discrepancy, normalization comparison and
  error absorption: replacing the main term changes the analytic contract.
- The numerical margin needed to preserve the public `0.67` count. An easier
  existence-only proof would not replace that public quantitative obligation.

## Order of work and acceptance conditions

First extract the primitive large-sieve core and separate the production triple
bridge from q¹ diagnostics. Next split the switching facade and share the
count-to-existence endgame. Then consolidate common analytic providers and
small repeated lemmas. Preserve historical interfaces through optional facades
where they serve other consumers.

After each real source change, rebuild the affected source closure, run both
public acceptance probes and recheck axioms. Before accepting the whole cleanup,
run the full main build and public-module replays; shared consumers include
Li–Liu. Research mirrors need their own manifest and validation updates if
changed. Recompute source sizes after the actual changes.

Narrowing a focused Chen import target does not automatically reduce a full
default build which still selects every library module by glob. The original audit did not claim removed lines or build-time gains. Its
measurements describe the pre-cleanup revision; the completed cleanup is
recorded separately above.
