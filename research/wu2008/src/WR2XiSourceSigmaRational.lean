import WR2XiCandidateCertificate
import W06SigmaV2

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Wu2008DoubleSieve NodeExtension

/-- Certified common sigma moment for the candidate's extended upper nodes. -/
theorem sigma_moment_lower : (1105570288/1000000000000 : ℝ) ≤
    aProfile (nineProfile RationalCandidate.lowerH) := by
  apply le_trans _ (WuTarget.W06.sigmaLower_le_aProfile RationalCandidate.lowerH_nonneg)
  norm_num [WuTarget.W06.sigmaLower, WuTarget.W06.sigmaCoeff, WuTarget.W06.massLower,
    WuTarget.W06.denominatorLower, RationalCandidate.lowerH, Fin.sum_univ_succ]

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.sigma_moment_lower
