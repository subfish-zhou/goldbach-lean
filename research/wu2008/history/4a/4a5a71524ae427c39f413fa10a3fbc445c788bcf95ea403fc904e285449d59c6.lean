import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerAssembly
import MathlibNt.Wu2008DoubleSieve.ImprovementIntegrals

/-!
# The actual coefficients on the compact sixth-term geometry

The frozen canonical API calls a(s) `wuLowerCoefficient`. The identity
below retains its defining s*f(s)/(2*exp(gamma)) at every point, including
the part above s = 4. No continuity of the improvement is asserted.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem truncatedSixthLower_classical_kernel {δ x y : ℝ}
    (hδ : 0 ≤ δ) (h : truncatedSixthLowerRegion δ x y) :
    4 * (wuLowerCoefficient (truncatedSixthLowerS δ x y) /
      (x * y * (truncatedSixthLowerC δ - x - y))) =
      (2 * exp (-eulerMascheroniConstant) / truncatedSixthLowerAlpha) *
        (jr1965f (truncatedSixthLowerS δ x y) / (x * y)) := by
  have hb := truncatedSixthLower_region_bounds hδ h
  have hd : 0 < truncatedSixthLowerC δ - x - y :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) truncatedSixthLower_parameters.1).trans_le hb.2.2.1
  unfold wuLowerCoefficient truncatedSixthLowerS
  rw [exp_neg]
  field_simp
  ring

theorem truncatedSixthLower_effective_monotone {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    MonotoneOn (fun s => wuLowerCoefficient s + wuImprovementLimit false δ s)
      (Icc 2 5) := by
  intro s hs t ht hst
  exact wu_effective_lower_limit_mono hδ (by linarith) (by linarith [hs.1])
    hst (by linarith [ht.2])

theorem truncatedSixthLower_effective_bounds {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hs : s ∈ Icc 2 5) :
    0 ≤ wuLowerCoefficient s + wuImprovementLimit false δ s ∧
      wuLowerCoefficient s + wuImprovementLimit false δ s ≤ 10 := by
  have hs1 : 1 ≤ s := by linarith [hs.1]
  have hs10 : s ≤ 10 := by linarith [hs.2]
  have hb := wuImprovementLimit_bounds hδ (by linarith) hs1 hs10
  have hf : 0 ≤ jr1965f s := jr1965f_nonneg (by linarith)
  have ha : 0 ≤ wuLowerCoefficient s := by unfold wuLowerCoefficient; positivity
  have hA : wuUpperCoefficient s ≤ 10 := by
    unfold wuUpperCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).mpr
    have hF := mul_le_mul_of_nonneg_left (jr1965F_le_delayConstant hs1) (by linarith : 0 ≤ s)
    unfold jr1965DelayConstant at hF
    nlinarith [exp_pos eulerMascheroniConstant]
  exact ⟨add_nonneg ha hb.2.2.1, (by linarith [hb.2.2.2])⟩

theorem truncatedSixthLower_effective_intervalIntegrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    IntervalIntegrable (fun s => wuLowerCoefficient s + wuImprovementLimit false δ s)
      volume 2 5 := by
  have hm := truncatedSixthLower_effective_monotone hδ hδhi
  rw [← uIcc_of_le (by norm_num : (2 : ℝ) ≤ 5)] at hm
  exact hm.intervalIntegrable

end Wu2008DoubleSieve
