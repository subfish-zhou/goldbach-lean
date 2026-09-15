import MathlibNt.Wu2008DoubleSieve.UnroundedFifthJPayments
import MathlibNt.Wu2008DoubleSieve.FourLogAffineBalance

namespace Wu2008DoubleSieve.UnroundedPayments
open Real

noncomputable def newBalance : ℝ :=
  BaseRecurrenceLower.newBase+fifthRational+RationalMovingSixth.rationalSixth+47/481250-
    VariableCoefficientBalance.rationalG-weightedJUpper-FourLogAffine.newFour

/-- Reassemble the actual original K first. The strict inequality is supplied by the fifth term. -/
theorem complete_coefficient_gt_newBalance :
    newBalance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := BaseRecurrenceLower.base_recurrence_lower
  have hg := VariableCoefficientBalance.full_G_rational
  have hj := original_weightedJ_le
  have hi := FourLogAffine.original_four_le_newFour
  have hp := fifthRational_lt_fifthPairFlin
  have hq := RationalMovingSixth.actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ VariableCoefficientBalance.rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient newBalance
  linarith

/-- Literal regression of every original positive and negative term and weight. -/
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

/-- Compare packages only after actual reassembly. -/
theorem exact_balance_gain : newBalance =
    FourLogAffine.newBalance+(fifthRational-3/2)+(12-weightedJUpper) := by
  unfold newBalance FourLogAffine.newBalance
  ring

theorem balance_strictly_improved : FourLogAffine.newBalance < newBalance := by
  rw [exact_balance_gain]
  linarith [fifthRational_gt_old,weightedJUpper_lt_old]

noncomputable def exactBalance : ℝ :=
  670722682979739294230518720643049159328852986728990752562220147372995382606701570798320654096424989761665931006304407589588523165449801883309441056040137794846920977734446746355831/
  325760824883814642339829488763961472006012999653215624059333105340134159003379834806075025954975306213913614508559371090525830321724955337904232996626742229237539242937830400000000

theorem newBalance_eq_exact : newBalance = exactBalance := by
  rw [exact_balance_gain,FourLogAffine.newBalance_eq_exact,fifthRational_eq]
  norm_num [FourLogAffine.exactBalance,exactBalance,weightedJUpper,j7Upper,j8Upper,j9Upper]

theorem newBalance_gt_two : (2 : ℝ) < newBalance := by
  rw [newBalance_eq_exact]
  norm_num [exactBalance]

theorem complete_coefficient_gt_two :
    (2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient :=
  newBalance_gt_two.trans complete_coefficient_gt_newBalance

/-- This payment is not the classical benchmark. -/
theorem newBalance_below_benchmark : newBalance < (899/250 : ℝ) := by
  rw [newBalance_eq_exact]
  norm_num [exactBalance]

/-- Actual epsilon is K minus the unrounded balance, not zero. -/
theorem actual_count_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) := by
  have hε : 0 < TruncatedElevenClassicalCountLower.classicalCoefficient-newBalance :=
    sub_pos.mpr complete_coefficient_gt_newBalance
  obtain ⟨T,hT,hcount⟩ :=
    TruncatedElevenClassicalCountLower.actual_count_lower_full_coefficient hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have h := hcount N hN he
  change (TruncatedElevenClassicalCountLower.classicalCoefficient-
    (TruncatedElevenClassicalCountLower.classicalCoefficient-newBalance))*
    wuSingularSeries N*N/log N^(2 : ℕ) ≤
    4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) at h
  rw [sub_sub_cancel] at h
  refine ⟨h,?_⟩
  have hid : (newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) =
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ))/4 := by ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [h])

/-- All three payments share exactly one threshold and the literal ordinary P2 carrier. -/
theorem actual_count_exact_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((670722682979739294230518720643049159328852986728990752562220147372995382606701570798320654096424989761665931006304407589588523165449801883309441056040137794846920977734446746355831/
        1303043299535258569359317955055845888024051998612862496237332421360536636013519339224300103819901224855654458034237484362103321286899821351616931986506968916950156971751321600000000 : ℝ)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,hcount⟩ := actual_count_same_threshold
  refine ⟨T,hT,?_⟩
  intro N hN he
  obtain ⟨hm,hc⟩ := hcount N hN he
  refine ⟨hm,hc,?_⟩
  have heq : newBalance/4 =
      (670722682979739294230518720643049159328852986728990752562220147372995382606701570798320654096424989761665931006304407589588523165449801883309441056040137794846920977734446746355831/
        1303043299535258569359317955055845888024051998612862496237332421360536636013519339224300103819901224855654458034237484362103321286899821351616931986506968916950156971751321600000000 : ℝ) := by
    rw [newBalance_eq_exact]
    norm_num [exactBalance]
  rw [heq] at hc
  exact hc

/-- Ordinary P2 includes complement one, with no factor-size restriction. -/
theorem complement_one_allowed {p : ℕ} (hp : Nat.Prime p) :
    p ∈ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements (p+1) :=
  FourLogAffine.complement_one_allowed hp

/-- Positivity excludes complement zero. -/
theorem complement_zero_excluded (N : ℕ) :
    N ∉ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N :=
  FourLogAffine.complement_zero_excluded N

end Wu2008DoubleSieve.UnroundedPayments
