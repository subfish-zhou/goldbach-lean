import WR2XiMixedEntryLower
import WR2XiRationalMixedArithmetic

/-! All thirty-six original second-functional candidate entries, with Gamma5 paid. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open WuPaper.R2Xi NodeExtension

theorem second_functional_entries (r : Fin 4) (k : Fin 9)
    (hsigma : (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    lowerMatrix (r.castAdd 5) k ≤ correctedNineMatrix (r.castAdd 5) k := by
  by_cases h : Xi2RationalTop.factors r 1 - 1 ≤ Xi2RationalTop.left k
  · exact Xi2RationalTop.top_corrected_entry r k h hsigma
  · exact Xi2RationalMixed.mixed_corrected_entry_of_arithmetic r k
      (Xi2RationalMixed.mixed_arithmetic r k (lt_of_not_ge h)) hsigma

end WuPaper.R2Xi.RationalCandidate
#print axioms WuPaper.R2Xi.RationalCandidate.second_functional_entries
