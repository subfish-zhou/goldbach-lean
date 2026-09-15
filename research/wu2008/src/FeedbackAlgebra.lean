import NodeTransfer
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedback

namespace ActualNineFeedback
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open scoped Interval BigOperators

noncomputable def deltaLoss (δ : ℝ) : ℝ := 2 * δ / (1 - 2 * δ)

noncomputable def coupledCostMass (p : SecondFunctionalParameters) : ℝ :=
  omega3XIntegralEnvelope p.kappa3 p.kappa1 + SecondFunctionalCoupled.jointSup p

noncomputable def coupledLoss (p : SecondFunctionalParameters) : ℝ :=
  2 * coupledCostMass p / 5

theorem deltaLoss_nonneg {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    0 ≤ deltaLoss δ := by
  unfold deltaLoss
  exact div_nonneg (by positivity) (by linarith)

theorem exact_cost_loss (p : SecondFunctionalParameters) {δ : ℝ}
    (hh : δ ≤ 1 / 10) :
    SecondFunctionalCoupledFeedback.cost p δ / 5 =
      (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
        SecondFunctionalCoupledFeedback.classical p + 2 * coupledCostMass p) / 5 +
      deltaLoss δ * coupledLoss p := by
  have hn : 1 - 2 * δ ≠ 0 := by linarith
  unfold SecondFunctionalCoupledFeedback.cost deltaLoss coupledLoss coupledCostMass
  field_simp
  ring

end ActualNineFeedback
