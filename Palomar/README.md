# Chen's theorem and the Li-Liu refinement

This publication contains the complete Chen and Li-Liu Lean proof libraries,
with an independent specification for three representation theorems.

Formalization author and maintainer — Ziyu Zhou.
[ORCID](https://orcid.org/0009-0009-7661-7545)

For every sufficiently large even natural number, Chen's theorem gives a prime
plus a prime or a product of two primes. The product's factors may be equal.
The Li-Liu refinement gives `N = p + r*q`, where `p` and `q` are prime, `r` is
one or prime, and `r^10 <= q^9`. Its equivalent real-power statement is included.
Each theorem chooses a common threshold before quantifying over the subsequent
natural numbers.

The main project also provides quantitative bounds. The Comparator configuration
selects the three qualitative statements described above.

## Reproduce

Install the pinned Lean toolchain, then run the following commands from the
publication root.

```sh
lake exe cache get
lake --wfail build
python3 scripts/check.py
lake --wfail build Palomar.Solution
lake comparator --config Palomar/comparator.json --paranoid
python3 scripts/check_palomar_sources.py .
```

`Palomar/Challenge.lean` states the result using Mathlib and carries deliberate
specification holes. `Palomar/Solution.lean` implements those statements through
the fully proved public project endpoints. Comparator checks their correspondence
and the permitted axioms. The retained main-library probes independently check
all six original public endpoints, including the quantitative constants.

## Verification status

The complete main build, six public endpoint checks and Lean kernel replays
pass. Local replay through Palomar's unmodified mechanical verification functions
accepts the independent Challenge and Solution with the bundled Lean and NanoDa.
The registry-pinned con-ron and the additional Lean paranoid, lean4lean and
con-leche checkers also accept the complete 1.53 GB export.

Five coefficient certificates check rational numerators and denominators through
a proved injectivity lemma. This removes the bundled NanoDa stack/memory failure.
The local replay uses bubblewrap 0.12.0, a separately compiled protected Challenge,
cgroup resource supervision and the standard three axioms. Builds reuse verified
caches. The hosted-provider capacity preflight runs during submission.
[Verification policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

## Provenance and review

`formalization.yaml` records the human author identifier, mathematical sources,
AI participation and review status. The historical production account
requires the maintainer's review before registration. Copyright and author
notices on inherited source modules are retained.

The earlier development and its separate research projects are available in the
original repository. The publication's source manifest identifies the bytes
included in this preparation. [Original project](https://github.com/subfish-zhou/goldbach-lean)

The mathematical sources include Chen's theorem, Zihao Liu's corrected proof and
the Li-Liu refinement. [Corrected Chen proof](https://arxiv.org/abs/2203.07871v1),
[Li-Liu paper](https://arxiv.org/abs/2606.05224v1)

## Register a reviewed snapshot

Commit and push the reviewed publication to a public repository. Select its full
40-character commit SHA, `Palomar/comparator.json` and `formalization.yaml` in
the Palomar submission form. The repository license is Apache-2.0.
