import WR2XiTightCertificate
import WR2XiRationalCandidate

/-! The tight sixth column is unaffected by the first-column Gamma5 correction. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open Wu2008DoubleSieve SecondFunctionalParameters NodeExtension

theorem tight_corrected_entry
    (hsigma : (Xi2RationalCheck.sigmaCoeff : ℝ) ≤ aProfile (nineProfile (nodeBasis 5))) :
    lowerMatrix 1 5 ≤ correctedNineMatrix 1 5 := by
  change (27/1000 : ℝ) ≤ Xi2CorrectedCoefficient 1 5
  simp only [Xi2CorrectedCoefficient, show (5:Fin 9) ≠ 0 by decide, if_false, sub_zero]
  exact Xi2RationalCheck.tight_original_entry hsigma

end WuPaper.R2Xi.RationalCandidate
#print axioms WuPaper.R2Xi.RationalCandidate.tight_corrected_entry
