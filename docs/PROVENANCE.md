# Source provenance and licensing

## Original project sources

The Chen implementation originates in
[UyNewNas/chen-theorem-lean](https://github.com/UyNewNas/chen-theorem-lean), with
substantial subsequent proof completion and engineering changes.
The reusable analytics sources originate in
[UyNewNas/analytic-number-theory-lean](https://github.com/UyNewNas/analytic-number-theory-lean)
and subsequent local development. This release includes the required local
source closure; it does not assert that those upstream repositories already
contain this completed version.

The source package is distributed under the existing Apache-2.0 license.
Existing copyright and author notices in upstream source files are retained.

## Adapted prime-number-theorem proof

The `PrimeNumberTheoremAnd/` sources are an adapted minimal import closure from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
release `v4.32.2`, commit
`6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`, under Apache-2.0.

The port uses Lean `v4.33.0-rc1` and the Mathlib revision pinned in this package.
Its documented adaptations include explicit measurability, unit-circle norm,
and almost-everywhere arguments in `Fourier.lean` and `Wiener.lean`, and an
obsolete redundant proof step in `MediumPNT.lean`. Three unused alternate decay
lemmas with unproved terms were not retained in the upstream import extraction.
The retained implementation is built and checked with the rest of the package;
it is not represented as a new independent proof of the prime number theorem.

## External Lean dependencies

`lake-manifest.json` records the exact Git revisions of Mathlib, LeanArchitect,
and their transitive dependencies. These packages are obtained by Lake; their
source trees and cached artifacts are not included in the release archive.
Their own licenses and attribution remain applicable.

## Mathematical sources

The implementation combines several sources rather than following one paper
line by line. The principal families are:

- J. R. Chen, *On the representation of a large even integer as the sum of a
  prime and the product of at most two primes*, Scientia Sinica 16 (1973), 157–176.
- The Jurkat–Richert linear-sieve and Richert weighted-sieve arguments, with
  precise source variants identified in the implementation module documentation.
- Suzuki's modern linear-sieve comparison results, used for the actual lower
  and upper source families rather than relabelled as the original 1965 theorem.
- Bombieri–Vinogradov and Pan-type averaged distribution estimates, including
  the proved weighted and switched-source specializations consumed here.
- Z. Liu, the Chen-theorem exposition and Selberg-sieve calculations associated
  with [arXiv:2203.07871](https://arxiv.org/abs/2203.07871).

Source references identify proof provenance; they are not additional axioms.
The acceptance checks report the formal dependency axioms of both public results.
