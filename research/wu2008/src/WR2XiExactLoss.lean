import WR2XiTriangleLoss

/-! The actual original Xi2 inequality with its exact Gamma5 loss retained. -/
noncomputable section
namespace WuPaper.R2Xi
open Wu2008DoubleSieve MotherPair SecondFunctionalCoupled ActualNineFeedback
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

/-- Actual full-minus-legal mother gain equals the scalar loss integral exactly. -/
theorem gamma5_mother_actual_loss (r : Fin 4) {δ : ℝ} (hd : 0 < δ) (hh : δ < 1/2) :
    (gamma5FullGain (gamma5OriginalRow r) δ -
      gainIntegral (gamma5OriginalRow r) .gammaFive δ)/5 =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v *
        generalKernel (rowParameters r).1 (rowParameters r).2 v := by
  have hp := gamma5_original_row_parameters r
  have hAB : 1/(gamma5OriginalRow r).S ≤ 1/(gamma5OriginalRow r).kappa2 := by
    rw [hp.1, hp.2]
    fin_cases r <;> norm_num [rowParameters]
  rw [gamma5_full_gain_eq_triangle, gamma5_legal_gain_eq_triangle _ _ hAB, hp.1, hp.2]
  exact gamma5_triangle_actual_loss r hd hh

/-- Exact analytic inequality: no constant Gamma5 overestimate is used. -/
theorem Xi2_four_rows_exact_loss (r : Fin 4) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    coupledBase (gamma5OriginalRow r) - deltaLoss δ * coupledLoss (gamma5OriginalRow r) +
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) -
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t *
        generalKernel (rowParameters r).1 (rowParameters r).2 t) ≤
      wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have hp : AnalyticParameters (gamma5OriginalRow r) := (coupledRow_geometry r).1
  have h := feedback_le_limit (gamma5OriginalRow r) hp hd hh
  unfold SecondFunctionalCoupled.feedback at h
  have he := paid_coefficient_original_identity r hd (by linarith : δ < 1/2)
  unfold gamma5PaidCoefficient at he
  have hXi := Xi2_actual_feedback hd hh (WuPaper.RMapMMatrix.original_four_rows_qualified r)
  change (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) ≤
    originalSecondFeedback δ (gamma5OriginalRow r) at hXi
  have hloss := gamma5_mother_actual_loss r hd (by linarith : δ < 1/2)
  have hbase := originalSecondCost_base (gamma5OriginalRow r) hh
  linarith only [h, he, hXi, hloss, hbase]

end WuPaper.R2Xi
