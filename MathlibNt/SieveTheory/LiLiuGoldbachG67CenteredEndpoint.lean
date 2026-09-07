import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral1
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral2
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral3
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral4
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral5

open MeasureTheory Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
namespace G67CenteredEvaluation
open G67Centered
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000

theorem centered_endpoint_bound : (54233/40000 : ℝ) ≤ G67Centered.polynomialIntegral - G67Centered.errorBudget := by
  unfold polynomialIntegral
  rw [integral1_eq, endpoint1_eq, integral2_eq, endpoint2_eq, integral3_eq, endpoint3_eq, integral4_eq, endpoint4_eq, integral5_eq, endpoint5_eq]
  norm_num [errorBudget, cutoff, a]

#check @centered_endpoint_bound
#print axioms centered_endpoint_bound
end G67CenteredEvaluation
