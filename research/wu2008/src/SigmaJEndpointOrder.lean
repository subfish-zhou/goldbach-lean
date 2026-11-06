import SigmaJEndpointRows

namespace SigmaJEndpoint
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment FirstErrorFullPayment
noncomputable section


theorem scales_ge_one {S A : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1) (hS5 : S ≤ 5) :
    1 ≤ firstScale S A ∧ 1 ≤ secondScale S A := by
  have hx : 1 ≤ (S-1)/A := (one_le_div (by linarith : 0 < A)).mpr hAS
  have hx2 : (S-1)/A ≤ 2 := (div_le_iff₀ (by linarith : 0 < A)).mpr (by linarith)
  have hy : 1 ≤ S-A := by linarith
  have hy3 : S-A ≤ 3 := by linarith
  have hf := coefficient_antitone hx hx2
  have hs := coefficient_antitone hy hy3
  norm_num [coefficient] at hf hs
  constructor
  · exact (one_le_div (by norm_num : (0:ℝ) < 4/7)).mpr hf
  · exact (one_le_div (by norm_num : (0:ℝ) < 9/17)).mpr hs



end
end SigmaJEndpoint
