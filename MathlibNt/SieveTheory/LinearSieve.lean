import MathlibNt.SieveTheory.LinearSieve.FiniteWeights
import MathlibNt.SieveTheory.LinearSieve.RosserChains
import MathlibNt.SieveTheory.LinearSieve.BoundaryMass
import MathlibNt.SieveTheory.LinearSieve.BoundaryRegularity
import MathlibNt.SieveTheory.LinearSieve.BoundaryIntegrals
import MathlibNt.SieveTheory.LinearSieve.UpperRosserDensity
import MathlibNt.SieveTheory.LinearSieve.SieveApplications

/-!
# MathlibNt.SieveTheory.LinearSieve

## Linear sieve / Jurkat-Richert estimates

The Jurkat-Richert theorem (1965) is a central tool for the lower bound on W(N)
in Chen's theorem. It expresses upper and lower sieve bounds in terms of
functions F(s) and f(s).

The differential-delay framework motivating the legacy outline uses:
  - F(s) = 2e^γ / s for 2 ≤ s ≤ 4;
  - f(s) = 0 for s ≤ 3;
  - (s·F(s))' = f(s-1) for s ≥ 4;
  - (s·f(s))' = F(s-1) for s ≥ 3,
where γ is the Euler-Mascheroni constant.

These legacy conventions are not a specification of the canonical
dimension-one sieve functions. In particular, `sieveFunctionF` and
`sieveFunctionf` in the imported `SieveApplications` module contain
placeholder branches and are used only in fixed-parameter remainder
interfaces. They do not establish the classical uniform estimates or
Chen's numerical constants. The finite lower-Möbius and generic Rosser
density interfaces are developed separately in the imported modules.

References:
  - Jurkat & Richert (1965), Acta Arith. 11, 217-240
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 8
  - Liu, Z. (2022), arXiv:2203.07871, §III
-/
