# Proof and software architecture

## Public boundary

`Goldbach.Statement` defines the literal mathematical target using only basic
Mathlib notions. `Goldbach.Theorem` instantiates that target and exposes the
quantitative representation bound. `Goldbach.Checks` is a test module, not an
import of the public library.

The package contains the complete local import closure needed by the theorem.
It does not depend on a sibling analytics checkout. Git dependencies are pinned;
ported sources that required local adaptation are included with attribution.

## Mathematical dependency layers

1. **Prime-distribution foundations.** The adapted prime-number-theorem proof
   feeds natural prime counting and Mertens estimates. The analytic layer also
   establishes character, large-sieve, and distribution estimates.
2. **Linear sieve.** Constructed Jurkat–Richert delay functions provide concrete
   majorants. Suzuki comparison results supply the lower and uniformly
   conditioned upper estimates needed for the actual Goldbach densities.
3. **Weighted lower bound.** The Richert finite chain combines the base lower
   sieve, conditioned upper sieve, squareful corrections, prime integrals, and
   weighted Bombieri–Vinogradov error control.
4. **Switched-source upper bound.** The proved Liu–Pan distribution statement
   is transported to the coprime, weighted source consumed by the Selberg
   upper-sieve calculation. The aggregate source sum is retained inside the
   absolute value at its defining boundary.
5. **Finite counting bridge.** Exact candidate, penalty, and representation
   counts preserve factor multiplicities, boundary fibres, and integer cutoffs.
   The weighted lower estimate minus the triple penalty yields the actual
   representation lower bound.
6. **Final existence.** Positivity produces a representation for every
   sufficiently large even integer, and the public facade expands the
   almost-prime predicate into primes and products.

## Important interface distinctions

The actual Goldbach source density is `1 / (p - 1)`, not the literal
Jurkat–Richert specialization `1 / p`. The proof connects these through the
constructed sieve functions and comparison theorems; it does not identify the
two source models.

The modern upper comparison is not attributed to the literal 1965 theorem.
Likewise, proving the endpoint does not claim to reproduce every formula in
Chen's original paper. Source-specific module names identify mathematical
inputs, not a claim of historical verbatim replication.

A failed historical counting premise must not be used as the release endpoint.
The final route uses corrected finite counting and the actual good-representation
set, with all remaining analytic premises supplied by proved theorems.

## Engineering rules

- Public theorem names and statement meanings are stable across source reorganization.
- Mathematical declaration namespaces need not match physical subdirectories;
  this keeps existing proof references stable while modules are grouped by topic.
- Source dependencies flow toward the public facade; tests do not become its imports.
- Standalone imports and private helpers are verified after module splitting.
- No experimental worktree, build artifact, task transcript, or internal report
  belongs to the public source tree.
- Unreachable modules are excluded from this release, not automatically declared
  mathematically invalid. Shared dependencies remain even if they also serve
  work beyond the release theorem.
