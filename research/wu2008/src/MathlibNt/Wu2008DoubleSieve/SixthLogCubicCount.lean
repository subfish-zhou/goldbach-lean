import MathlibNt.Wu2008DoubleSieve.SixthLogCubicPayment
import MathlibNt.Wu2008DoubleSieve.GConvexChordCount

namespace Wu2008DoubleSieve.SixthLogCubicCorrection
open Real SharpLogRecurrence

noncomputable def newBalance : ℝ :=
  BaseRecurrenceLower.newBase+UnroundedPayments.fifthRational+
    RationalMovingSixth.rationalSixth+SixthReciprocalCorrection.deltaSixth+deltaLog+47/481250-GConvexChord.rationalG-
    UnroundedPayments.weightedJUpper-FourLogAffine.newFour

/-- The fifth-term strict lower bound survives actual signed reassembly. -/
theorem complete_coefficient_gt_newBalance :
    newBalance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := BaseRecurrenceLower.base_recurrence_lower
  have hg := GConvexChord.full_G_rational
  have hj := UnroundedPayments.original_weightedJ_le
  have hi := FourLogAffine.original_four_le_newFour
  have hp := UnroundedPayments.fifthRational_lt_fifthPairFlin
  have hq := actual_sixth_ge_rational_corrected
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ GConvexChord.rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient newBalance
  linarith

theorem literal_complete_coefficient_gt_newBalance :
    newBalance <
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
      truncatedSixthLowerF6lin+47/481250-
      SingleUpperClassicalLimit.Glin (1/3)-
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-8*J9-
      16*SeventhEighth.J7-8*SeventhEighth.J8-
      8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 :=
  complete_coefficient_gt_newBalance

/-- Package comparison is downstream of the signed actual coefficient theorem. -/
theorem exact_balance_gain : newBalance = SixthReciprocalCorrection.newBalance+deltaLog := by
  unfold newBalance SixthReciprocalCorrection.newBalance
  ring

theorem balance_strictly_improved : SixthReciprocalCorrection.newBalance < newBalance := by
  rw [exact_balance_gain]
  linarith only [deltaLog_pos]

noncomputable def exactBalance : ℝ := SixthReciprocalCorrection.exactBalance+
  1187400847683322048386560078365256261041294877546103876976007289970830388271148310198906709618961179/7545885901676678275919158598554354710005799650469246322063206213824795976825339983586567540013665636

theorem newBalance_eq_exact : newBalance = exactBalance := by
  rw [exact_balance_gain,SixthReciprocalCorrection.newBalance_eq_exact,deltaLog_exact]
  rfl

noncomputable def exactQuarter : ℝ := exactBalance/4

theorem quarter_eq_exact : newBalance/4 = exactQuarter := by
  rw [newBalance_eq_exact]
  rfl

noncomputable def actualEpsilon : ℝ :=
  TruncatedElevenClassicalCountLower.classicalCoefficient-newBalance

theorem actualEpsilon_pos : 0 < actualEpsilon :=
  sub_pos.mpr complete_coefficient_gt_newBalance

/-- One threshold pays the coefficient, its quarter, and the expanded ordinary P2 count. -/
theorem actual_count_exact_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      (exactQuarter*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,hcount⟩ :=
    TruncatedElevenClassicalCountLower.actual_count_lower_full_coefficient actualEpsilon_pos
  refine ⟨T,hT,?_⟩
  intro N hN he
  have h := hcount N hN he
  change (TruncatedElevenClassicalCountLower.classicalCoefficient-
    (TruncatedElevenClassicalCountLower.classicalCoefficient-newBalance))*
    wuSingularSeries N*N/log N^(2 : ℕ) ≤
    4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) at h
  rw [sub_sub_cancel] at h
  have hc : (newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    have hid : (newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) =
        (newBalance*wuSingularSeries N*N/log N^(2 : ℕ))/4 := by ring
    rw [hid]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [h])
  refine ⟨h,hc,?_⟩
  rw [quarter_eq_exact] at hc
  exact hc

theorem complement_one_allowed {p : ℕ} (hp : Nat.Prime p) :
    p ∈ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements (p+1) :=
  UnroundedPayments.complement_one_allowed hp

theorem complement_zero_excluded (N : ℕ) :
    N ∉ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N :=
  UnroundedPayments.complement_zero_excluded N

/-- All three unrounded payments are expressed with the same exact balance and the same T. -/
theorem exact_count_three_payments :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (exactBalance*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      (exactQuarter*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      (exactQuarter*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := actual_count_exact_same_threshold
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  rw [quarter_eq_exact,newBalance_eq_exact] at hn
  exact hn

end Wu2008DoubleSieve.SixthLogCubicCorrection
