import E07FifthPolynomial

namespace WuTarget.E07Fifth
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
noncomputable section

theorem final_lower :
    (87760644803325371/14970763715034960000000 : ℝ) ≤
      (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 :=
  fifth_balance_lower

theorem final_positive :
    (0 : ℝ) < 87760644803325371/14970763715034960000000 := by
  norm_num

theorem paid_exact :
    W14.fifthGainLower = (134930927046659/13229419344750000000 : ℝ) :=
  W14.fifth_gain_lower_exact

theorem net_amount_exact :
    (4*polynomialPrimitive b-W14.fifthGainLower)/4 =
      (87760644803325371/14970763715034960000000 : ℝ) := by
  have h := net_identity
  dsimp only [netCredit] at h
  linarith only [h]

theorem net_accounting_identity :
    (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 =
      87760644803325371/14970763715034960000000 +
        (PositiveCoreResume.fifthGain-4*polynomialPrimitive b)/4 := by
  have h := net_amount_exact
  linarith only [h]

theorem original_profile_identity :
    (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 =
      (∫ v : ℝ × ℝ, fifthPairRegion.indicator (fun v =>
        (11/2-max 4 ((1/2-v.1-v.2)/a))^3/70875 /
          (v.1*v.2*(1/2-v.1-v.2))) v) -
        (134930927046659/13229419344750000000)/4 := by
  rw [paid_exact]
  simp only [PositiveCoreResume.fifthGain, PositiveCoreResume.fifthMinorant,
    PositiveCoreResume.fifthProfile, truncatedSixthLowerS, truncatedSixthLowerC,
    sub_zero, a]
  ring

theorem original_profile_balance_lower :
    (87760644803325371/14970763715034960000000 : ℝ) ≤
      (∫ v : ℝ × ℝ, fifthPairRegion.indicator (fun v =>
        (11/2-max 4 ((1/2-v.1-v.2)/a))^3/70875 /
          (v.1*v.2*(1/2-v.1-v.2))) v) -
        (134930927046659/13229419344750000000)/4 := by
  rw [← original_profile_identity]
  exact final_lower

set_option pp.fullNames true in
#check final_lower
set_option pp.fullNames true in
#check final_positive
set_option pp.fullNames true in
#check paid_exact
set_option pp.fullNames true in
#check polynomial_gain_lower
set_option pp.fullNames true in
#check polynomial_gain_exact
set_option pp.fullNames true in
#check net_amount_exact
set_option pp.fullNames true in
#check net_accounting_identity
set_option pp.fullNames true in
#check original_profile_identity
set_option pp.fullNames true in
#check original_profile_balance_lower
#print axioms final_lower
#print axioms final_positive
#print axioms polynomial_gain_lower
#print axioms polynomial_gain_exact
#print axioms net_amount_exact
#print axioms net_accounting_identity
#print axioms original_profile_identity
#print axioms original_profile_balance_lower

end
end WuTarget.E07Fifth
