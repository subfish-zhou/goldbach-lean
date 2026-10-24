import WR2GammaHighCoupledFixed
import Wu04RemainingStrongPaid

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve ActualNineFeedback Wu08OriginalPsiRecovery
open Wu04RemainingCore Wu04RemainingStrongPublication Wu04RemainingStrongCompleteCost
open Real

theorem classicalEight_identity (j : Fin 3) :
    classicalEight j = 5*wuUpperCoefficient (row j).s-classicalNumerator (row j) := by
  have h := coupledBase_eq_original_logs (coupledRow_geometry j.succ)
  change coupledBase (row j) = (classicalNumerator (row j)-2*coupledCostMass (row j))/5 at h
  unfold coupledBase at h
  unfold classicalEight signedClassical
  linarith only [h]

theorem publication_coefficient (j : Fin 3) {δ : ℝ}
    (hd : 0 < δ) (hr : δ ≤ Wu04RemainingStrongPaid.deltaRadius j) :
    classicalEight j + (2/(1-2*δ))*(omega3XIntegralEnvelope (row j).kappa3 (row j).kappa1+
      SecondFunctionalCoupled.jointSup (row j)) ≤ 5*(wuUpperCoefficient (row j).s-publication j) := by
  have hh : δ ≤ 1/10 := hr.trans (min_le_left _ _)
  have hden : 0 < 1-2*δ := by linarith
  have hb := Wu04RemainingStrongPaid.publication_budget_with_slack j
  have hc := Wu04RemainingStrongCompleteCost.complete_paid j
  have hs := Wu04RemainingStrongPaid.deltaDebit_le_slack j hd hr
  have herr : (2/(1-2*δ)-2)*coupledCostMass (row j) ≤ slack j := by
    have hfactor : 0 ≤ 2/(1-2*δ)-2 := by
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hden).mpr
      linarith
    have hmul := mul_le_mul_of_nonneg_left hc hfactor
    have hid : (2/(1-2*δ)-2)*costCap j = 5*Wu04RemainingStrongPaid.deltaDebit j δ := by
      unfold Wu04RemainingStrongPaid.deltaDebit
      field_simp
      ring
    rw [hid] at hmul
    linarith only [hmul,hs]
  rw [classicalEight_identity]
  change _ + (2/(1-2*δ))*coupledCostMass (row j) ≤ _
  linarith only [hb,herr]

end WuPaper.R2GammaHigh
#print axioms WuPaper.R2GammaHigh.publication_coefficient
