import WR2XiSourceLowerCertificate
import WR2XiSourceFifth
import WSrcFifthGainAnalyticConsumer

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Real NodeExtension Finset WuSource.SrcFifthGain
open scoped Classical

theorem fifth_rational_paid : Analytic.rationalGain lowerLower ≤ SourceFifth.amount := by
  have hm : Analytic.rationalGain lowerLower ≤ Analytic.rationalGain CandidateGrid.lower := by
    unfold Analytic.rationalGain directedGain
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
    apply sum_le_sum
    intro j hj
    have hj13 := mem_range.mp hj
    exact mul_le_mul_of_nonneg_left (lowerLower_le_original (by omega) (by omega))
      (Analytic.thirteen_positive_weights hj13).1.le
  exact hm.trans (Analytic.rational_gain_le_grid
    (fun j hj => CandidateGrid.lower_nonneg (by omega)))

theorem fifth_gain_lower : (1297/1000000 : ℝ) ≤ SourceFifth.amount := by
  apply le_trans _ fifth_rational_paid
  rw [Analytic.rational_gain_literal]
  norm_num [lowerLower, lowerNumerator]

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.fifth_gain_lower
