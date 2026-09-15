import MathlibNt.Wu2008DoubleSieve.FourLogAffineRational
import MathlibNt.Wu2008DoubleSieve.BaseRecurrenceCarrier

namespace Wu2008DoubleSieve.FourLogAffine
open Real SharpLogRecurrence

noncomputable def newBalance : ℝ :=
  BaseRecurrenceLower.newBase+3/2+RationalMovingSixth.rationalSixth+47/481250-
    VariableCoefficientBalance.rationalG-12-newFour

/-- Reassemble the original full K from the actual positive lower and negative upper producers. -/
theorem complete_coefficient_gt_newBalance :
    newBalance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := BaseRecurrenceLower.base_recurrence_lower
  have hg := VariableCoefficientBalance.full_G_rational
  have hj := SharpJBalance.weighted_J_lt_twelve
  have h4 := original_four_le_newFour
  have hp := SharpMassBalance.fifth_gt_three_halves
  have hq := RationalMovingSixth.actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ VariableCoefficientBalance.rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient newBalance
  linarith

/-- The payment difference is compared only after the actual K has been reassembled. -/
theorem exact_balance_gain : newBalance = BaseRecurrenceLower.newBalance+(21/20-newFour) := by
  unfold newBalance BaseRecurrenceLower.newBalance
  ring

theorem balance_strictly_improved : BaseRecurrenceLower.newBalance < newBalance := by
  rw [exact_balance_gain]
  linarith [newFour_lt_old]

theorem newBalance_pos : 0 < newBalance :=
  BaseRecurrenceLower.newBalance_pos.trans balance_strictly_improved

/-- Literal regression: all original weights, both G terms, and both original fourfold masses. -/
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

noncomputable def exactBalance : ℝ :=
  288456083195586583790899322687285842234658473180999635023085472022915921575183506917007091716155912856260159579815615057319182399/
  152174190298990431806451667401428618834322333713124409151916978175574505808897245998894167417357371174161313587946603801600000000

theorem newBalance_eq_exact : newBalance = exactBalance := by
  rw [exact_balance_gain,BaseRecurrenceLower.newBalance_eq_exact]
  norm_num [BaseRecurrenceLower.exactBalance,exactBalance,newFour,tenUpper,elevenUpper,
    l,u,w,lowerLog,upperLog,FourRoughClosedMass.alpha,FourRoughClosedMass.beta,
    FourRoughClosedMass.lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem newBalance_below_benchmark : newBalance < (899/250 : ℝ) := by
  rw [newBalance_eq_exact]
  norm_num [exactBalance]

/-- Unconditional actual consumption with epsilon = K-newBalance and one threshold. -/
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

/-- Both symbolic and literal exact rational payments hold at the SAME T. -/
theorem actual_count_exact_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (newBalance*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((newBalance/4)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((288456083195586583790899322687285842234658473180999635023085472022915921575183506917007091716155912856260159579815615057319182399/
        608696761195961727225806669605714475337289334852497636607667912702298023235588983995576669669429484696645254351786415206400000000 : ℝ)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,hcount⟩ := actual_count_same_threshold
  refine ⟨T,hT,?_⟩
  intro N hN he
  obtain ⟨hm,hc⟩ := hcount N hN he
  refine ⟨hm,hc,?_⟩
  have heq : newBalance/4 =
      (288456083195586583790899322687285842234658473180999635023085472022915921575183506917007091716155912856260159579815615057319182399/
        608696761195961727225806669605714475337289334852497636607667912702298023235588983995576669669429484696645254351786415206400000000 : ℝ) := by
    rw [newBalance_eq_exact]
    norm_num [exactBalance]
  rw [heq] at hc
  exact hc

/-- Ordinary P2: complement one is allowed; no factor-size restriction is introduced. -/
theorem complement_one_allowed {p : ℕ} (hp : Nat.Prime p) :
    p ∈ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements (p+1) :=
  BaseRecurrenceLower.complement_one_allowed hp

/-- Complement zero is excluded by positivity. -/
theorem complement_zero_excluded (N : ℕ) :
    N ∉ MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N :=
  BaseRecurrenceLower.complement_zero_excluded N

end Wu2008DoubleSieve.FourLogAffine
