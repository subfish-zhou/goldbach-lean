# Source provenance and licensing

## Original project sources

The completed Chen (1+2) implementation builds on
[UyNewNas/chen-theorem-lean](https://github.com/UyNewNas/chen-theorem-lean), with
substantial subsequent proof completion and engineering changes. The reusable
analytics sources originate in
[UyNewNas/analytic-number-theory-lean](https://github.com/UyNewNas/analytic-number-theory-lean)
and subsequent local development. This package brings together the required
local source closure and the changes that complete the released proof.

The source package is distributed under the existing Apache-2.0 license.
Existing copyright and author notices in upstream source files are retained.

## Adapted prime-number-theorem proof

The `PrimeNumberTheoremAnd/` sources are an adapted minimal import closure from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
release `v4.32.2`, commit
`6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`, under Apache-2.0.

The port uses Lean `v4.33.0-rc1` and the Mathlib revision pinned in this package.
Its documented adaptations make measurability, unit-circle norm, and
almost-everywhere arguments explicit in `Fourier.lean` and `Wiener.lean`, and
remove an obsolete redundant proof step in `MediumPNT.lean`. The import
extraction also omits three unused alternate decay lemmas that contained
unproved terms. The retained implementation carries the upstream proof into
this toolchain and is built and checked with the rest of the package.

## External Lean dependencies

`lake-manifest.json` records the exact Git revisions of Mathlib, LeanArchitect,
and their transitive dependencies. Lake fetches these packages separately from
the release archive, which excludes their source trees and cached artifacts.
Their own licenses and attribution remain applicable.

## Mathematical sources

The implementation assembles the completed Chen theorem from the following
mathematical sources. Module documentation identifies the source variants and
adaptations used at each step.

- J. R. Chen, *On the representation of a large even integer as the sum of a
  prime and the product of at most two primes*, Scientia Sinica 16 (1973), 157–176.
- The Jurkat–Richert linear-sieve and Richert weighted-sieve arguments, with
  precise source variants identified in the implementation module documentation.
- Suzuki's modern linear-sieve comparison results, which supply comparisons for
  the actual lower and upper source families. The modern upper comparison is
  attributed to Suzuki; the Jurkat–Richert modules document the 1965 input.
- Bombieri–Vinogradov and Pan-type averaged distribution estimates, including
  the proved weighted and switched-source specializations consumed here.
- Z. Liu, the Chen-theorem exposition and Selberg-sieve calculations associated
  with [arXiv:2203.07871](https://arxiv.org/abs/2203.07871).

Source references record the mathematical provenance of the Lean proofs.
The acceptance checks report the formal dependency axioms of both public results.
