import E02JointCreditPayment

noncomputable section
namespace WuTarget.E02JointCredit
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators

theorem actual_jointCredit_lower :
    (8508808767/793830625000000000 : ℝ) ≤ W17Accepted.jointCredit :=
  amount_le_jointCredit

theorem actual_jointCredit_gt :
    (1/100000000 : ℝ) < W17Accepted.jointCredit :=
  amount_gt_simple.trans_le amount_le_jointCredit

theorem actual_lowGain_difference_lower :
    4 * (8508808767/793830625000000000 : ℝ) ≤
      W01.lowGain W17Accepted.enhanced - W01.lowGain W04Accepted.enhanced := by
  have h := actual_jointCredit_lower
  rw [W17Accepted.jointCredit_eq] at h
  linarith only [h]

theorem actual_coefficient_gain :
    W01.ordinaryCoefficient W04Accepted.enhanced +
      (8508808767/793830625000000000 : ℝ) ≤
        W01.ordinaryCoefficient W17Accepted.enhanced := by
  have h := actual_jointCredit_lower
  unfold W17Accepted.jointCredit at h
  linarith only [h]

theorem paid_budget_gain :
    W13TightAccepted.paidCoefficient + amount ≤ W17Accepted.paidCoefficient :=
  add_le_add_right amount_le_jointCredit _

theorem remaining_budget_gain :
    W13TightAccepted.remainingCoefficient + amount ≤
      W17Accepted.remainingCoefficient :=
  add_le_add_right amount_le_jointCredit _

theorem net_amount_identity :
    W01.ordinaryCoefficient W17Accepted.enhanced =
      W01.ordinaryCoefficient W04Accepted.enhanced + amount +
        (W17Accepted.jointCredit - amount) := by
  unfold W17Accepted.jointCredit
  ring

theorem net_remainder_nonneg : 0 ≤ W17Accepted.jointCredit - amount :=
  sub_nonneg.mpr amount_le_jointCredit

theorem ordinary_P2_with_amount {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, W17Accepted.enhanced i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix W17Accepted.enhanced j ≤
        wuImprovementLimit false δ (rNode (j.val+1))) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (W01.ordinaryCoefficient W04Accepted.enhanced +
          (8508808767/793830625000000000 : ℝ) - ε) * U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ, hd, hm, hs, hx, hn, T, hT, hc⟩ :=
    W17Accepted.enhanced_ordinary_P2 hε hdmax
  refine ⟨δ, hd, hm, hs, hx, hn, T, hT, ?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right actual_coefficient_gain ε)
    hM).trans (hc N hN he)

#check @difference_eq
#print axioms difference_eq
#check @difference_remainders_nonneg
#print axioms difference_remainders_nonneg
#check @increment_le_difference
#print axioms increment_le_difference
#check @transferredDifference_eq
#print axioms transferredDifference_eq
#check @transferredDifference_nonneg
#print axioms transferredDifference_nonneg
#check @jointCredit_eq_gamma
#print axioms jointCredit_eq_gamma
#check @jointCredit_eq_weights
#print axioms jointCredit_eq_weights
#check @paid_difference_lower
#print axioms paid_difference_lower
#check @rational_difference_lower
#print axioms rational_difference_lower
#check @first_transfer_paid
#print axioms first_transfer_paid
#check @first_difference_paid
#print axioms first_difference_paid
#check @amount_eq
#print axioms amount_eq
#check @actual_jointCredit_lower
#print axioms actual_jointCredit_lower
#check @actual_jointCredit_gt
#print axioms actual_jointCredit_gt
#check @actual_lowGain_difference_lower
#print axioms actual_lowGain_difference_lower
#check @actual_coefficient_gain
#print axioms actual_coefficient_gain
#check @paid_budget_gain
#print axioms paid_budget_gain
#check @remaining_budget_gain
#print axioms remaining_budget_gain
#check @net_amount_identity
#print axioms net_amount_identity
#check @net_remainder_nonneg
#print axioms net_remainder_nonneg
#check @ordinary_P2_with_amount
#print axioms ordinary_P2_with_amount
#check @W03.Gamma_eq_weights
#print axioms W03.Gamma_eq_weights
#check @W03.paid_weights_consumer
#print axioms W03.paid_weights_consumer
#print amount
#print difference
#print transferredDifference
#print addedMatrix

end WuTarget.E02JointCredit
