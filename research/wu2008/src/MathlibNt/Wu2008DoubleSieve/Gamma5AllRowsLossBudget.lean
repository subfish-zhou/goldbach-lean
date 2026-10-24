import MathlibNt.Wu2004MeanValue.GammaFiveTriangleBudget
import MathlibNt.Wu2008DoubleSieve.Gamma5GainKernel

/-!
# Actual Gamma₅ full-minus-legal loss for all four parameter rows

The weight in these integrals is the actual `wuImprovementLimit`. The clipped
extension is used only to obtain global measurability and boundedness, and is
removed using the ratio range of the original triangle.
-/

namespace Wu2008DoubleSieve
open Real Set MeasureTheory Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

/-- Clipping does not change either actual triangular gain in an original row. -/
theorem gamma5_row_triangle_unclip (i : Fin 4) (legal : Bool) (δ : ℝ) :
    triangleGain (rowParameters i).1 (rowParameters i).2 legal (gamma5GainH δ) =
      triangleGain (rowParameters i).1 (rowParameters i).2 legal
        (wuImprovementLimit true δ) := by
  have hp : 0 < (rowParameters i).1 ∧ 1/(rowParameters i).1 ≤ (rowParameters i).2 ∧
      1 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) ∧ (rowParameters i).1 ≤ 5 := by
    fin_cases i <;> norm_num [rowParameters]
  apply triangleGain_congr_on hp.1 hp.2.1 legal
  intro v hv
  have hv' : v ∈ Icc (1 : ℝ) 3 := ⟨hp.2.2.1.trans hv.1,by linarith [hv.2,hp.2.2.2]⟩
  simp only [gamma5GainH, gamma5Gain_clip_eq hv']

/-- Actual full and legal gains, before the second functional's factor one fifth. -/
theorem gamma5_original_row_loss_lt (i : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    triangleGain (rowParameters i).1 (rowParameters i).2 false (wuImprovementLimit true δ) -
      triangleGain (rowParameters i).1 (rowParameters i).2 true (wuImprovementLimit true δ) <
        5*rowDebit i/2 := by
  have h := original_row_triangle_gain_budget i (gamma5GainH δ)
    (gamma5Gain_H_antitone hδ hδhi).measurable (gamma5Gain_H_bounds hδ hδhi)
  simpa only [gamma5_row_triangle_unclip] using h

/-- Normalized actual losses: less than 1/1500, 1/1000, 9/8000 and 1/2000. -/
theorem gamma5_original_row_normalized_loss_lt (i : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    (triangleGain (rowParameters i).1 (rowParameters i).2 false (wuImprovementLimit true δ) -
      triangleGain (rowParameters i).1 (rowParameters i).2 true (wuImprovementLimit true δ))/5 <
        rowDebit i/2 := by
  have h := gamma5_original_row_loss_lt i hδ hδhi
  linarith

end Wu2008DoubleSieve
