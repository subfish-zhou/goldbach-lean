import PrimeNumberTheoremAnd.MediumPNT

/-!
# Prime-distribution API

This module is the stable facade over the ported PNTAnd implementation.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open scoped Chebyshev

/-- A medium-strength prime number theorem for Chebyshev's psi function. -/
theorem chebyshevPsi_medium_error :
    ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
  MediumPNT


end AnalyticNumberTheory.PrimeDistribution
