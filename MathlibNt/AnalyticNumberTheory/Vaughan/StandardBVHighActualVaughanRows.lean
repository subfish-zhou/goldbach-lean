

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVHighHybridFeasibility
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVChosenSmallSquare

/-!
 # Actual Vaughan square ledgers produce the moving high source

The sole analytic input in this file is a square-ledger theorem for the three
literal Vaughan coefficient rows on the retained primitive-conductor interval.
In particular, it is not an estimate for the final unsquared high mean.  The
fixed exponent `κ` is the complete reserve for shell counts, prefix maxima,
Möbius/logarithmic convolution coefficients, and the conductor/Abel envelopes.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section


lemma highConductorSet_eq_interval (N Q C : ℕ)
    (hR : 1 ≤ logConductorThreshold N C) :
    highConductorSet N Q C =
      Finset.Icc (logConductorThreshold N C + 1) Q := by
  ext d
  simp only [highConductorSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hdQ⟩, hRd⟩
    exact ⟨Nat.add_one_le_iff.mpr hRd, hdQ⟩
  · rintro ⟨hRd, hdQ⟩
    exact ⟨⟨by omega, hdQ⟩, Nat.add_one_le_iff.mp hRd⟩


end
end AnalyticNumberTheory.LargeSieve
