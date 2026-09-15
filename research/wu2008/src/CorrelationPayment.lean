import SignedTotalCorrelation

namespace Wu2008DoubleSieve.CorrelationPayment
open Real
noncomputable section

/-- The unchanged ordinary-P2 carrier, in both source and expanded forms. -/
def CountBound (L : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (L*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      (L*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ))

/-- Spend the actual positive gap in the already proved unrounded family. -/
theorem pay {L : ℝ} (hL : L < JointHMotherPayment.unroundedCoefficient) :
    CountBound L := by
  have h := JointHMotherPayment.unrounded_ordinary_P2_same_threshold
    (JointHMotherPayment.unroundedCoefficient-L) (sub_pos.mpr hL)
  simpa only [CountBound, sub_sub_cancel] using h

/-- Full fixed correlation gain; no half-gain loss and no addition of count bounds. -/
theorem full_fixed_count : CountBound SignedTotalCorrelation.lowerCoefficient :=
  pay SignedTotalCorrelation.joint_actual_lower

/-- Keep the actual nonnegative logarithmic residual, not a numerical surrogate. -/
def residualCoefficient : ℝ :=
  SignedTotalCorrelation.lowerCoefficient+SignedTotalCorrelation.retainedResidual/4

theorem residual_coefficient_lt :
    residualCoefficient < JointHMotherPayment.unroundedCoefficient :=
  SignedTotalCorrelation.joint_actual_residual_lower

theorem full_residual_count : CountBound residualCoefficient :=
  pay residual_coefficient_lt

theorem residual_coefficient_identity :
    residualCoefficient = JointHMotherPayment.lowerCoefficient+
      SignedTotalCorrelation.correlationGain/4+SignedTotalCorrelation.retainedResidual/4 := by
  rw [residualCoefficient, SignedTotalCorrelation.fixed_improvement_identity]

theorem residual_strict_improvement :
    JointHMotherPayment.lowerCoefficient+1/80 < residualCoefficient := by
  have h := SignedTotalCorrelation.fixed_gain_gt_one_eightieth
  have hr := SignedTotalCorrelation.retainedResidual_nonneg
  unfold residualCoefficient
  linarith

#print axioms full_fixed_count
#print axioms full_residual_count
#print axioms residual_strict_improvement
end
end Wu2008DoubleSieve.CorrelationPayment
