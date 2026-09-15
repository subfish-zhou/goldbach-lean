import MathlibNt.Wu2008DoubleSieve.FourPositiveLogLower

namespace Wu2008DoubleSieve.FourPositiveRationalLower
open Real FourRoughClosedMass FourPositiveLogLower SharpLogRecurrence

noncomputable def rationalTail : ℝ := lowerLog (beta/alpha)
noncomputable def rationalCross : ℝ := lowerLog ((lam-beta)/beta)
noncomputable def rationalTen : ℝ := rationalTail^4/(48*beta)
noncomputable def rationalEleven : ℝ := rationalCross*rationalTail^3/(12*beta)
noncomputable def weightedRational : ℝ := 8*rationalTen+8*rationalEleven

theorem tail_log_identity : tailLog = log (beta/alpha) := by
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  exact (log_div hb.ne' ha.ne').symm

theorem cross_log_identity : crossLog = log ((lam-beta)/beta) := by
  have hb := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  have hc : 0 < lam-beta := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  exact (log_div hc.ne' hb.ne').symm

theorem rational_logs_positive : 0 < rationalTail ∧ 0 < rationalCross := by
  norm_num [rationalTail,rationalCross,lowerLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem rational_logs_lower : rationalTail ≤ tailLog ∧ rationalCross ≤ crossLog := by
  rw [tail_log_identity,cross_log_identity]
  constructor
  · exact log_lower (by norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  · exact log_lower (by norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda])

theorem actual_ten_lower : rationalTen ≤ I10 := by
  obtain ⟨ht,_⟩ := rational_logs_lower
  have ht0 := rational_logs_positive.1.le
  have hp := pow_le_pow_left₀ ht0 ht 4
  have hb := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  exact (div_le_div_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ 48*beta)).trans I10_log_lower

theorem actual_eleven_lower : rationalEleven ≤ I11 := by
  obtain ⟨ht,hc⟩ := rational_logs_lower
  obtain ⟨ht0,hc0⟩ := rational_logs_positive
  have hp := pow_le_pow_left₀ ht0.le ht 3
  have hprod := mul_le_mul hc hp (pow_nonneg ht0.le _) (hc0.le.trans hc)
  have hb := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  exact (div_le_div_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ 12*beta)).trans I11_log_lower

theorem rational_masses_positive : 0 < rationalTen ∧ 0 < rationalEleven := by
  obtain ⟨ht,hc⟩ := rational_logs_positive
  have hb := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  constructor <;> dsimp only [rationalTen, rationalEleven] <;> positivity

theorem actual_masses_positive : 0 < I10 ∧ 0 < I11 :=
  ⟨rational_masses_positive.1.trans_le actual_ten_lower,
    rational_masses_positive.2.trans_le actual_eleven_lower⟩

/-- The original two negative terms retain their respective weights eight and eight. -/
theorem actual_weighted_lower : weightedRational ≤ 8*I10+8*I11 := by
  have ht := actual_ten_lower
  have he := actual_eleven_lower
  unfold weightedRational
  linarith

theorem weighted_positive : 0 < weightedRational := by
  obtain ⟨ht,he⟩ := rational_masses_positive
  unfold weightedRational
  positivity

/-- Both original literal fourfold integrals have positive rational lower packages. -/
theorem literal_actual_lower :
    0 < rationalTen ∧ rationalTen ≤
      (∫ x in alpha..beta, ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..beta, kernel x y z t) ∧
    0 < rationalEleven ∧ rationalEleven ≤
      (∫ x in alpha..beta, ∫ y in x..beta, ∫ z in y..beta, ∫ t in beta..lam-z, kernel x y z t) :=
  ⟨rational_masses_positive.1,actual_ten_lower,rational_masses_positive.2,actual_eleven_lower⟩

end Wu2008DoubleSieve.FourPositiveRationalLower
