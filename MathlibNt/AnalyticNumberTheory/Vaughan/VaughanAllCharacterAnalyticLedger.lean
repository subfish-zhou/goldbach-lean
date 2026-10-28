

import MathlibNt.AnalyticNumberTheory.LargeSieve.VonMangoldtConductorCorrection
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
 # All-character nonprincipal Vaughan ledger and Type-II scale audit

This module only assembles proved producers.  It keeps the principal character
out, keeps the full prefix maximum on the all-character side, and records that
the currently proved tensor Type-II estimate is only an endpoint estimate.
Consequently no Standard Bombieri--Vinogradov theorem is claimed.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The coefficient `1`, used to specialize Vaughan's identity to `Λ`. -/
def vaughanUnitIntegerCoeff (_ : ℤ) : ℂ := 1


lemma vaughanLambdaCoeff_unit_eq (n : ℤ) :
    vaughanLambdaCoeff vaughanUnitIntegerCoeff n = vonMangoldtIntegerCoeff n := by
  simp [vaughanLambdaCoeff, vaughanUnitIntegerCoeff, vonMangoldtIntegerCoeff]


end

end AnalyticNumberTheory.LargeSieve
