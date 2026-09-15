import Hf4ActualLog

noncomputable section
namespace Hf4Actual
open Real Set TerminalE SigmaVariableOuterPayment SigmaVariableFull

theorem ratio_caps {t : ℝ} (ht : t ∈ Icc 1 3) :
    zeroRatio t ≤ 2 ∧ negRatio t ≤ 2 ∧ quadRatio t ≤ 2 ∧ radRatio t ≤ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have h2 : t^2 ≤ 9 := by nlinarith [ht.1,ht.2]
  have h3 := mul_le_mul_of_nonneg_right ht.2 (sq_nonneg t)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg t)
  have h2t := mul_le_mul_of_nonneg_right ht.2 ht0.le
  refine ⟨?_,?_,?_,?_⟩
  · unfold zeroRatio
    linarith [ht.2]
  · unfold negRatio
    apply (div_le_iff₀ (by positivity : 0 < 6*(t+1))).mpr
    nlinarith only [h2t,ht.1]
  · unfold quadRatio
    apply (div_le_iff₀ (by positivity : 0 < 90*(t+1)^2)).mpr
    nlinarith only [h3,h4,sq_nonneg t,ht.1]
  · have hr3 : 3 ≤ radical := by nlinarith only [radical_sq,radical_pos]
    have hprod := mul_nonneg (show 0 ≤ 3*radical-5 by linarith)
      (show 0 ≤ 3-t by linarith [ht.2])
    unfold radRatio
    apply (div_le_iff₀ (mul_pos (by linarith [radical_pos] : 0 < t+9+2*radical)
      (by linarith [radical_lt_four] : 0 < 5-radical))).mpr
    nlinarith only [hprod,radical_sq,radical_lt_four]

theorem coefficient_caps {t : ℝ} (ht : t ∈ Icc 1 3) :
    -logZeroCoeff (-(t+1)) ≤ 100 ∧ logNegCoeff (-(t+1)) ≤ 100 ∧
    logQuadCoeff (-(t+1)) ≤ 100 ∧ logRadCoeff (-(t+1)) ≤ 100 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have h2 : t^2 ≤ 9 := by nlinarith [ht.1,ht.2]
  have h3 : t^3 ≤ 27 := by nlinarith only [mul_le_mul_of_nonneg_right ht.2 (sq_nonneg t),h2]
  have h4 : t^4 ≤ 81 := by
    nlinarith only [mul_le_mul h2 h2 (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 9)]
  have h4lo : 1 ≤ t^4 := one_le_pow₀ ht.1
  have hq : 11 ≤ -t^2+6*t+6 := by
    nlinarith only [mul_nonneg (show 0 ≤ t-1 by linarith [ht.1])
      (show 0 ≤ 5-t by linarith [ht.2])]
  have hq0 : 0 < -t^2+6*t+6 := by linarith
  have hr3 : 3 ≤ radical := by nlinarith only [radical_sq,radical_pos]
  have hprod : (33:ℝ) ≤ radical*(-t^2+6*t+6) := by
    have hh := mul_le_mul hr3 hq (by norm_num : (0:ℝ) ≤ 11) radical_pos.le
    norm_num at hh
    exact hh
  refine ⟨?_,?_,?_,?_⟩
  · rw [zero_coefficient_formula ht.1,neg_div,neg_neg]
    apply (div_le_iff₀ (by positivity : 0 < 210*(t+1)^2)).mpr
    nlinarith only [sq_nonneg t,ht.1]
  · rw [neg_coefficient_formula ht.1]
    apply (div_le_iff₀ (by positivity : 0 < 945*t^4)).mpr
    nlinarith only [h4,h3,h4lo,sq_nonneg t,ht.1]
  · rw [quad_coefficient_formula ht]
    apply (div_le_iff₀ (by positivity : 0 < 189*(-t^2+6*t+6))).mpr
    nlinarith only [hq,sq_nonneg t,ht.2]
  · rw [rad_coefficient_formula ht]
    apply (div_le_iff₀ (by positivity : 0 < 189*radical*(-t^2+6*t+6))).mpr
    nlinarith only [hprod,sq_nonneg t,ht.2]

theorem outer_weight_upper {t : ℝ} (ht : t ∈ Icc 1 3) :
    SigmaVariableFull.weight t ≤ paidWeight t+(1/1250:ℝ) := by
  have hc := coefficient_caps ht
  have hr := ratio_caps ht
  have h0 := split_errors ⟨zeroRatio_ge ht.1,hr.1⟩
  have h1 := split_errors ⟨negRatio_ge ht.1,hr.2.1⟩
  have hq := split_errors ⟨quadRatio_ge ht.1,hr.2.2.1⟩
  have hh := split_errors ⟨radRatio_ge ht.1,hr.2.2.2⟩
  have a0 := mul_le_mul hc.1 h0.2
    (sub_nonneg.mpr (RemainingHf.le_splitUpper (zeroRatio_ge ht.1))) (by norm_num : (0:ℝ) ≤ 100)
  have a1 := mul_le_mul hc.2.1 h1.1
    (sub_nonneg.mpr (RemainingHf.splitLower_le (negRatio_ge ht.1))) (by norm_num : (0:ℝ) ≤ 100)
  have aq := mul_le_mul hc.2.2.1 hq.1
    (sub_nonneg.mpr (RemainingHf.splitLower_le (quadRatio_ge ht.1))) (by norm_num : (0:ℝ) ≤ 100)
  have ar := mul_le_mul hc.2.2.2 hh.1
    (sub_nonneg.mpr (RemainingHf.splitLower_le (radRatio_ge ht.1))) (by norm_num : (0:ℝ) ≤ 100)
  have hm : collectedMass t-paidMass t ≤ (1/1250:ℝ) := by
    rw [Hf4Outer.mass_loss_identity ht.1]
    linarith only [a0,a1,aq,ar]
  have hd : (collectedMass t-paidMass t)/t ≤ (1/1250:ℝ) := by
    apply (div_le_iff₀ (by linarith [ht.1] : 0 < t)).mpr
    nlinarith only [hm,ht.1]
  rw [sub_div] at hd
  unfold SigmaVariableFull.weight paidWeight
  rw [← collectedMass_identity]
  linarith only [hd]

end Hf4Actual
