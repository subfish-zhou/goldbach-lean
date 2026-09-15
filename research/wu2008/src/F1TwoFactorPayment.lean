import F1TwoFactorJoint
namespace F1TwoFactor
open Real Wu2008DoubleSieve FirstCRationalPayment F1JointFTC F1ActualSecondFTC F1SecondLogRecovery
noncomputable section

def jointLower : ℝ :=
  (1+commonB)*F1JointSplit.twoUpper+F1JointSplit.paid (1+commonB) (3/2)+
  F1JointSplit.paid 1 (1127/600)+F1JointSplit.paid commonA (3884129/3606400)+
  F1JointSplit.paid commonAC (4508/2927)+F1JointSplit.paid (-commonB) (2400/2381)+
  F1JointSplit.paid residueD (4508/3981)+F1JointSplit.paid baseCoefficient (2254/1727)+
  F1JointSplit.paid oneMinus crossOneMinus+F1JointSplit.paid (-onePlus) crossOnePlus+
  F1JointSplit.paid twoMinus crossTwoMinus+F1JointSplit.paid (-twoPlus) crossTwoPlus+
  rationalEndpointPart+F1JointFTC.rationalPart+rationalPartTwo+secondPayment+EJoint.payment

theorem jointLower_le_mass : jointLower ≤ jointMass := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  have h0 := mul_le_mul_of_nonpos_left F1JointSplit.log_two_le common_signs.2.2.2.1
  have h1 := F1JointSplit.paid_le (1+commonB) (by norm_num : (1:ℝ)≤3/2)
  have h2 := F1JointSplit.paid_le 1 (by norm_num : (1:ℝ)≤1127/600)
  have h3 := F1JointSplit.paid_le commonA (by norm_num : (1:ℝ)≤3884129/3606400)
  have h4 := F1JointSplit.paid_le commonAC (by norm_num : (1:ℝ)≤4508/2927)
  have h5 := F1JointSplit.paid_le (-commonB) (by norm_num : (1:ℝ)≤2400/2381)
  have h6 := F1JointSplit.paid_le residueD (by norm_num : (1:ℝ)≤4508/3981)
  have h7 := F1JointSplit.paid_le baseCoefficient (by norm_num : (1:ℝ)≤2254/1727)
  have h8 := F1JointSplit.paid_le oneMinus hxm
  have h9 := F1JointSplit.paid_le (-onePlus) hxp
  have h10 := F1JointSplit.paid_le twoMinus hym
  have h11 := F1JointSplit.paid_le (-twoPlus) hyp
  unfold jointLower jointMass
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

theorem jointLower_le_actual : 8*jointLower ≤ Wu08TerminalAlignment.firstMain := by
  linarith only [jointLower_le_mass,jointMass_le_actual]

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*jointLower-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*jointLower+ε := by
    linarith only [jointLower_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*jointLower+ε)=
      8*jointLower-ε := by ring
  simpa only [hid] using h N hN hEven
end
end F1TwoFactor
