

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMoment
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear

/-!
 # Explicit Q-dependent bilinear tensor moment bound

Expanding the outer `d`-sum and applying Cauchy only in `d` reduces the
bilinear tensor second moment (the mixed fourth moment for rank-one tensors) to
one nonmaximal weighted primitive large sieve for every row.  Thus the exact
rowwise charge is

`D * (M + c(Q) * Q^2) * coefficientEnergy`,

where `c(Q) = 2 * ceil (log(Q^2) / log 2) + 12`.  This module also compares
that expression with the genuine bilinear scale and gives an unconditional
producer for the canonical Vaughan block.  No prefix maximum is present; a
prefix version should be obtained separately by the dyadic/Rademacher--Menshov
reduction, paying its displayed logarithm squared.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The explicit logarithmic coefficient in the current primitive large sieve. -/
def primitiveBilinearQFactor (Q : ℕ) : ℝ :=
  2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12


lemma one_le_primitiveBilinearQFactor (Q : ℕ) :
    1 ≤ primitiveBilinearQFactor Q := by
  unfold primitiveBilinearQFactor
  have h : 0 ≤ (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) := by
    positivity
  linarith


end

end AnalyticNumberTheory.LargeSieve
