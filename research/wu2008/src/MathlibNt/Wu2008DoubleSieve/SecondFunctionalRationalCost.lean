import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMomentUpper
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalDirectedLUpper

namespace Wu2008DoubleSieve.SecondFunctionalRationalCost
open SecondFunctionalGeometricMass SecondFunctionalGeometricMass.Elementary
open SecondFunctionalFourSevenths Omega3ElementaryFeedback

/-- Exact cancellation first: only lower masses and Omega receive four sevenths. -/
theorem cost_equal_end (p : SecondFunctionalParameters) (hs : 0 < p.s)
    (hr : p.kappa3 = p.s) :
    omegaCost p + elementaryCap p =
      (4/7)*(elementaryMomentOne 1 (1/p.kappa1) (1/p.s) +
        Real.log ((1/p.s)/(1/p.kappa2))*elementaryMomentZero 1 (1/p.kappa1) (1/p.kappa2) +
        Real.log ((1/p.kappa2)/(1/p.kappa1))*elementaryMomentOne 0 (1/p.kappa2) (1/p.s) +
        lowerThreeLog p +
        Real.log ((1/p.kappa1)/(1/p.S))*elementaryMomentOne 0 (1/p.kappa2) (1/p.s)) +
      elementaryMomentOne 2 (1/p.kappa2) (1/p.s)/2 := by
  have hi : 0 < 1/p.s := one_div_pos.mpr hs
  unfold omegaCost elementaryCap elementaryMass elementaryLowerMass lowerFiveLog
    HighUnitSource.unitLogCap20 HighUnitSource.unitLogCap21
  simp only [hr, elementaryMomentOne_self _ hi, div_self hi.ne', Real.log_one,
    zero_mul, mul_zero, zero_div, add_zero, zero_add, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 5 ≠ 0)]
  ring

 theorem reciprocal_ratio (A B : ℝ) : (1/B)/(1/A) = A/B := by
  simp only [one_div, div_inv_eq_mul]
  ring

noncomputable def rationalCost (S k c s : ℝ) : ℝ :=
  (4/7)*((k-s)^3/(6*s^2) +
    ((c-s)/s)*((k-c)^2/(2*c)) +
    ((k-c)/c)*((c-s)^2/(2*s)) +
    ((S-k)/k)*(k-c)*((c-s)/s) +
    ((S-k)/k)*((c-s)^2/(2*s))) + (c-s)^4/(24*s^3)

 theorem cost_upper (p : SecondFunctionalParameters) (hs : 0 < p.s)
    (hsc : p.s ≤ p.kappa2) (hck : p.kappa2 ≤ p.kappa1)
    (hkS : p.kappa1 ≤ p.S) (hr : p.kappa3 = p.s) :
    omegaCost p + elementaryCap p ≤ rationalCost p.S p.kappa1 p.kappa2 p.s := by
  have hc := hs.trans_le hsc
  have hk := hc.trans_le hck
  obtain ⟨hcs0,hcs⟩ := log_ratio_upper hs hsc
  obtain ⟨hkc0,hkc⟩ := log_ratio_upper hc hck
  obtain ⟨hSk0,hSk⟩ := log_ratio_upper hk hkS
  have h01 := momentOne_upper 0 hs hsc
  have h11 := momentOne_upper 1 hs (hsc.trans hck)
  have h21 := momentOne_upper 2 hs hsc
  have h10 := momentZero_upper 1 hc hck
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add,
    pow_one, one_mul] at h01 h11 h21 h10
  have h01cap : 0 ≤ (p.kappa2-p.s)^2/(2*p.s) := by positivity
  have h10cap : 0 ≤ (p.kappa1-p.kappa2)^2/(2*p.kappa2) := by positivity
  have h1 := mul_le_mul h10 hcs hcs0 h10cap
  have h2 := mul_le_mul h01 hkc hkc0 h01cap
  have h4 := mul_le_mul h01 hSk hSk0 h01cap
  have h3a := mul_le_mul_of_nonneg_right hSk (sub_nonneg.mpr hck)
  have h3 := mul_le_mul h3a hcs hcs0
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hkS) hk.le) (sub_nonneg.mpr hck))
  have h21half : elementaryMomentOne 2 (1/p.kappa2) (1/p.s)/2 ≤
      (p.kappa2-p.s)^4/(24*p.s^3) := by
    convert! div_le_div_of_nonneg_right h21 (by norm_num : 0 ≤ (2 : ℝ)) using 1
    field_simp
    ring
  rw [cost_equal_end p hs hr]
  simp only [reciprocal_ratio, lowerThreeLog, one_div_one_div]
  unfold rationalCost
  nlinarith only [h11,h21half,h1,h2,h3,h4]

 theorem row3_cost_upper : omegaCost SecondFunctionalParameters.row3 +
    elementaryCap SecondFunctionalParameters.row3 ≤ 4577792210969/66653798400000 := by
  have h := cost_upper SecondFunctionalParameters.row3
    (by norm_num [SecondFunctionalParameters.row3])
    (by norm_num [SecondFunctionalParameters.row3])
    (by norm_num [SecondFunctionalParameters.row3])
    (by norm_num [SecondFunctionalParameters.row3]) rfl
  norm_num [rationalCost, SecondFunctionalParameters.row3] at h ⊢
  exact h

 theorem row4_cost_upper : omegaCost SecondFunctionalParameters.row4 +
    elementaryCap SecondFunctionalParameters.row4 ≤ 31667784024997/755387500000000 := by
  have h := cost_upper SecondFunctionalParameters.row4
    (by norm_num [SecondFunctionalParameters.row4])
    (by norm_num [SecondFunctionalParameters.row4])
    (by norm_num [SecondFunctionalParameters.row4])
    (by norm_num [SecondFunctionalParameters.row4]) rfl
  norm_num [rationalCost, SecondFunctionalParameters.row4] at h ⊢
  exact h

theorem row3_cost_lt : omegaCost SecondFunctionalParameters.row3 +
    elementaryCap SecondFunctionalParameters.row3 < 7/100 :=
  row3_cost_upper.trans_lt (by norm_num)

theorem row4_cost_lt : omegaCost SecondFunctionalParameters.row4 +
    elementaryCap SecondFunctionalParameters.row4 < 1/20 :=
  row4_cost_upper.trans_lt (by norm_num)

/-- The unchanged actual envelope and joint supremum consume the certified cap. -/
theorem row3_original_cost_upper :
    omega3XIntegralEnvelope
        SecondFunctionalParameters.row3.kappa3 SecondFunctionalParameters.row3.kappa1 +
      SecondFunctionalCoupled.jointSup SecondFunctionalParameters.row3 ≤
      4577792210969/66653798400000 := by
  have ho := Omega3ElementaryFeedback.original_envelope_le (2 : Fin 4)
  have hj := original_jointSup_elementary (2 : Fin 4)
  exact (add_le_add ho hj).trans row3_cost_upper

theorem row4_original_cost_upper :
    omega3XIntegralEnvelope
        SecondFunctionalParameters.row4.kappa3 SecondFunctionalParameters.row4.kappa1 +
      SecondFunctionalCoupled.jointSup SecondFunctionalParameters.row4 ≤
      31667784024997/755387500000000 := by
  have ho := Omega3ElementaryFeedback.original_envelope_le (3 : Fin 4)
  have hj := original_jointSup_elementary (3 : Fin 4)
  exact (add_le_add ho hj).trans row4_cost_upper

end Wu2008DoubleSieve.SecondFunctionalRationalCost
