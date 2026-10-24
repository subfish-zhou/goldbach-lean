import WR2XiMotherGain
import MathlibNt.Wu2008DoubleSieve.MotherPairGamma5FeedbackPaid

/-! The original Xi2 kernel in the actual four-row inequality, with a proved debit. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair SecondFunctionalCoupled
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

/-- All baseline costs retained by the actual mother; only delta remains variable. -/
def originalSecondCost (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4*wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
    classicalIntegral p .gammaFive + classicalIntegral p .gammaSix +
    classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight +
    (2/(1-2*δ))*(omega3XIntegralEnvelope p.kappa3 p.kappa1 + jointSup p) -
    fourthRowClassicalJ p.s p.S - fourthRowClassicalJ p.kappa2 p.S - fourthRowClassicalJ p.kappa3 p.S

private theorem row_fullH (r : Fin 4) : FullHParameters (gamma5OriginalRow r) := by
  fin_cases r
  · exact row1_fullH
  · exact row2_fullH
  · exact row3_fullH
  · exact row4_fullH

private theorem row_geometry (r : Fin 4) :
    WuPaper.RMapMMatrix.PropositionFourGeometry (gamma5OriginalRow r) :=
  WuPaper.RMapMMatrix.original_four_rows_qualified r

theorem paid_coefficient_original_identity (r : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gamma5PaidCoefficient r δ = originalSecondCost (gamma5OriginalRow r) δ -
      5*originalSecondFeedback δ (gamma5OriginalRow r) + 5*rowDebit r/2 := by
  have hp := row_geometry r
  obtain ⟨_,hS,hS5,_,_,_,hsS,h2S,h3S,hr2,hr3⟩ := second_parameter_bounds hp
  have ha := (row_fullH r).toAnalyticParameters
  have hs := ha.two_lt_s
  have hk3 := hs.trans_le ha.mother.s_le_kappa3
  have hk2 := hk3.trans ha.mother.kappa3_lt_kappa2
  have hr := hp.2.2.2.2.2.2.2.2.1
  rw [originalSecondFeedback_eq_mother_gains (row_fullH r) hδ hδhi]
  unfold gamma5PaidCoefficient coefficient originalSecondCost fourIntegralUpper
  rw [SecondFunctionalSignedCore.J_split hδ hδhi hs.le hsS.le hS hS5 hr,
    SecondFunctionalSignedCore.J_split hδ hδhi hk2.le h2S.le hS hS5 hr2,
    SecondFunctionalSignedCore.J_split hδ hδhi hk3.le h3S.le hS hS5 hr3]
  unfold actualLowerJ SecondFunctionalSignedCore.lowerGain
  ring

/-- Genuine original Xi2 feedback, with the normalized Gamma5 debit explicit.
No numerical lower bound for the baseline is assumed or asserted here. -/
theorem Xi2_four_rows_paid (r : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient (gamma5OriginalRow r).s -
      originalSecondCost (gamma5OriginalRow r) δ / 5 +
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) -
      rowDebit r/2 ≤ wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have h := gamma5_paid_actual_limit r hδ hδhi
  rw [paid_coefficient_original_identity r hδ (by linarith)] at h
  have hXi := Xi2_actual_feedback hδ hδhi (row_geometry r)
  linarith only [h,hXi]

/-- Reuse the existing baseline and delta-loss interface exactly. -/
theorem originalSecondCost_base (p : SecondFunctionalParameters) {δ : ℝ}
    (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient p.s - originalSecondCost p δ / 5 =
      ActualNineFeedback.coupledBase p -
        ActualNineFeedback.deltaLoss δ * ActualNineFeedback.coupledLoss p := by
  have hc := ActualNineFeedback.exact_cost_loss p hδhi
  unfold SecondFunctionalCoupledFeedback.cost SecondFunctionalCoupledFeedback.classical at hc
  unfold originalSecondCost ActualNineFeedback.coupledBase SecondFunctionalCoupledFeedback.classical
  linarith only [hc]

/-- The original Xi2 integral now uses the same baseline as the existing certificates. -/
theorem Xi2_four_rows_paid_base (r : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ActualNineFeedback.coupledBase (gamma5OriginalRow r) -
      ActualNineFeedback.deltaLoss δ * ActualNineFeedback.coupledLoss (gamma5OriginalRow r) +
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) -
      rowDebit r/2 ≤ wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have h := Xi2_four_rows_paid r hδ hδhi
  rw [originalSecondCost_base _ hδhi] at h
  exact h

end WuPaper.R2Xi
