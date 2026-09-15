import WE02JointCreditRankOnePayment

noncomputable section
namespace WuTarget.E02JointCredit
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators

theorem rankOne_actual_jointCredit_lower :
    (91/500000 : ℝ) ≤ W17Accepted.jointCredit :=
  rankOneAmount_le_jointCredit

theorem rankOne_actual_lowGain_difference_lower :
    (91/125000 : ℝ) ≤
      W01.lowGain W17Accepted.enhanced - W01.lowGain W04Accepted.enhanced := by
  have h := rankOne_actual_jointCredit_lower
  rw [W17Accepted.jointCredit_eq] at h
  linarith only [h]

theorem rankOne_actual_coefficient_gain :
    W01.ordinaryCoefficient W04Accepted.enhanced + (91/500000 : ℝ) ≤
      W01.ordinaryCoefficient W17Accepted.enhanced := by
  have h := rankOne_actual_jointCredit_lower
  unfold W17Accepted.jointCredit at h
  linarith only [h]

theorem rankOne_paid_budget_gain :
    W13TightAccepted.paidCoefficient + (91/500000 : ℝ) ≤
      W17Accepted.paidCoefficient :=
  add_le_add_right rankOne_actual_jointCredit_lower _

theorem rankOne_remaining_budget_gain :
    W13TightAccepted.remainingCoefficient + (91/500000 : ℝ) ≤
      W17Accepted.remainingCoefficient :=
  add_le_add_right rankOne_actual_jointCredit_lower _

theorem rankOneUpgrade_exact :
    rankOneUpgrade = (144468664941233/793830625000000000 : ℝ) := by
  norm_num [rankOneUpgrade, rankOneAmount, amount]

theorem rankOne_remaining_net_identity :
    W17Accepted.remainingCoefficient =
      W13TightAccepted.remainingCoefficient + amount + rankOneUpgrade +
        (W17Accepted.jointCredit - rankOneAmount) := by
  unfold W17Accepted.remainingCoefficient rankOneUpgrade
  ring

theorem rankOne_coefficient_net_identity :
    W01.ordinaryCoefficient W17Accepted.enhanced =
      W01.ordinaryCoefficient W04Accepted.enhanced + amount + rankOneUpgrade +
        (W17Accepted.jointCredit - rankOneAmount) := by
  unfold W17Accepted.jointCredit rankOneUpgrade
  ring

theorem ordinary_P2_rankOne_amount {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, W17Accepted.enhanced i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix W17Accepted.enhanced j ≤
        wuImprovementLimit false δ (rNode (j.val+1))) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (W01.ordinaryCoefficient W04Accepted.enhanced + (91/500000 : ℝ) - ε) *
            U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ, hd, hm, hs, hx, hn, T, hT, hc⟩ :=
    W17Accepted.enhanced_ordinary_P2 hε hdmax
  refine ⟨δ, hd, hm, hs, hx, hn, T, hT, ?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right rankOne_actual_coefficient_gain ε) hM).trans (hc N hN he)

theorem ordinary_P2_rankOne_budget {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (W13TightAccepted.paidCoefficient + (91/500000 : ℝ) - ε) *
            U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ, hd, hm, hs, T, hT, hc⟩ := W17Accepted.ordinary_P2_paid hε hdmax
  refine ⟨δ, hd, hm, hs, T, hT, ?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right rankOne_paid_budget_gain ε) hM).trans (hc N hN he)

#check @sigma_le_addedMatrix
#print axioms sigma_le_addedMatrix
#check @rankOne_apply
#print axioms rankOne_apply
#check @rankOneRows_le_difference
#print axioms rankOneRows_le_difference
#check @rankOne_remainder_eq
#print axioms rankOne_remainder_eq
#check @rankOne_remainder_nonneg
#print axioms rankOne_remainder_nonneg
#check @rankOne_rational_payment
#print axioms rankOne_rational_payment
#check @rankOneSigmaMass_exact
#print axioms rankOneSigmaMass_exact
#check @rankOneRowLower_le
#print axioms rankOneRowLower_le
#check @rankOneRowLower_le_difference
#print axioms rankOneRowLower_le_difference
#check @rankOneTransferLower_le_q
#print axioms rankOneTransferLower_le_q
#check @rankOneQTransfer_cast
#print axioms rankOneQTransfer_cast
#check @rankOneTransferLower_le_rational
#print axioms rankOneTransferLower_le_rational
#check @rankOneTransferLower_le_actual
#print axioms rankOneTransferLower_le_actual
#check @rankOneWeightedPayment_le
#print axioms rankOneWeightedPayment_le
#check @rankOneAmount_paid
#print axioms rankOneAmount_paid
#check @rankOne_actual_jointCredit_lower
#print axioms rankOne_actual_jointCredit_lower
#check @rankOneAmount_improves_old
#print axioms rankOneAmount_improves_old
#check @rankOneAmount_preserves_old
#print axioms rankOneAmount_preserves_old
#check @rankOneUpgrade_exact
#print axioms rankOneUpgrade_exact
#check @rankOneUpgrade_pos
#print axioms rankOneUpgrade_pos
#check @rankOneUpgrade_lower
#print axioms rankOneUpgrade_lower
#check @rankOneUpgrade_paid
#print axioms rankOneUpgrade_paid
#check @rankOne_net_identity
#print axioms rankOne_net_identity
#check @rankOne_net_remainder_nonneg
#print axioms rankOne_net_remainder_nonneg
#check @rankOne_actual_lowGain_difference_lower
#print axioms rankOne_actual_lowGain_difference_lower
#check @rankOne_actual_coefficient_gain
#print axioms rankOne_actual_coefficient_gain
#check @rankOne_paid_budget_gain
#print axioms rankOne_paid_budget_gain
#check @rankOne_remaining_budget_gain
#print axioms rankOne_remaining_budget_gain
#check @rankOne_remaining_net_identity
#print axioms rankOne_remaining_net_identity
#check @rankOne_coefficient_net_identity
#print axioms rankOne_coefficient_net_identity
#check @ordinary_P2_rankOne_amount
#print axioms ordinary_P2_rankOne_amount
#check @ordinary_P2_rankOne_budget
#print axioms ordinary_P2_rankOne_budget
#print rankOneSigmaMass
#print rankOneRows
#print rankOneRowLower
#print rankOneTransferLower
#print rankOneWeightedPayment
#print rankOneAmount
#print rankOneUpgrade

end WuTarget.E02JointCredit
