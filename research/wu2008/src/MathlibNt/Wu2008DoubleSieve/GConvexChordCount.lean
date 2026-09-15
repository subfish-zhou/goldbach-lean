import MathlibNt.Wu2008DoubleSieve.GConvexChordIntegral
import MathlibNt.Wu2008DoubleSieve.UnroundedCoefficientCount

namespace Wu2008DoubleSieve.GConvexChord
open Real SharpLogRecurrence
open VariableGIntegral (a s c logCoefficient linearCoefficient)

/-- Only the prescribed middle segment is replaced; all other payments are unchanged. -/
noncomputable def rationalG : ℝ :=
  (8/a)*(42823/151875)*upperLog (c 5/a)+
    8*((m/a+2*C)*upperLog (c 4/c 5)+2*C*upperLog (5/4))+
    8*(logCoefficient*upperLog (s/c 4)+linearCoefficient*(s-c 4)-
      (s^2-(c 4)^2)/(24*a^3)+11*upperLog (4/3))+8*upperLog (6*a/s)

theorem full_G_rational :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤ rationalG := by
  have h := full_G_upper
  rw [VariableGIntegral.endpoint] at h
  have h1 := log_upper (t := c 5/a)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,a,truncatedSixthLowerAlpha])
  have h2 := log_upper (t := c 4/c 5)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
  have h3 := log_upper (t := s/c 4)
    (by norm_num [s,c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_upper (t := (4/3 : ℝ)) (by norm_num)
  have h5 := log_upper (t := 6*a/s)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h6 := log_upper (t := (5/4 : ℝ)) (by norm_num)
  unfold rationalG endpoint at *
  norm_num [m,C,r4,r5,logCoefficient,linearCoefficient,a,truncatedSixthLowerAlpha] at h h1 h5 ⊢
  linarith

noncomputable def newBalance : ℝ :=
  BaseRecurrenceLower.newBase+UnroundedPayments.fifthRational+
    RationalMovingSixth.rationalSixth+47/481250-rationalG-
    UnroundedPayments.weightedJUpper-FourLogAffine.newFour

/-- The fifth-term strict lower bound survives actual signed reassembly. -/
theorem complete_coefficient_gt_newBalance :
    newBalance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := BaseRecurrenceLower.base_recurrence_lower
  have hg := full_G_rational
  have hj := UnroundedPayments.original_weightedJ_le
  have hi := FourLogAffine.original_four_le_newFour
  have hp := UnroundedPayments.fifthRational_lt_fifthPairFlin
  have hq := RationalMovingSixth.actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ rationalG at hg
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

/-- Package algebra is established after the actual bound, not substituted for it. -/
theorem exact_balance_gain : newBalance = UnroundedPayments.newBalance+
    (VariableCoefficientBalance.rationalG-rationalG) := by
  unfold newBalance UnroundedPayments.newBalance
  ring

theorem exact_G_gain : VariableCoefficientBalance.rationalG-rationalG =
    (33485718377/190855389375 : ℝ) := by
  norm_num [VariableCoefficientBalance.rationalG,rationalG,m,C,r4,r5,
    logCoefficient,linearCoefficient,upperLog,a,s,c,
    SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

theorem balance_strictly_improved : UnroundedPayments.newBalance < newBalance := by
  rw [exact_balance_gain,exact_G_gain]
  linarith

/-- This exact rational expression is not rounded to a convenient headline. -/
noncomputable def exactBalance : ℝ :=
  UnroundedPayments.exactBalance+33485718377/190855389375

theorem newBalance_eq_exact : newBalance = exactBalance := by
  rw [exact_balance_gain,exact_G_gain,UnroundedPayments.newBalance_eq_exact]
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

end Wu2008DoubleSieve.GConvexChord
