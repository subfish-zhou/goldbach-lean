import MathlibNt.Wu2008DoubleSieve.FourLogAffineMass
import MathlibNt.Wu2008DoubleSieve.SharpLogRecurrence

namespace Wu2008DoubleSieve.FourLogAffine
open Real FourRoughClosedMass ClassicalLogFourBounds SharpLogRecurrence

noncomputable def l : ℝ := lowerLog (beta/alpha)
noncomputable def u : ℝ := upperLog (beta/alpha)
noncomputable def w : ℝ := upperLog ((lam-alpha)/beta)
noncomputable def tenUpper : ℝ := (4/7)*(u^4/(24*alpha)-l^5/(60*beta))
noncomputable def elevenUpper : ℝ := (4/7)*w*(u^3/(6*alpha)-l^4/(12*beta))
noncomputable def newFour : ℝ := 8*tenUpper+8*elevenUpper

theorem fixed_log_bounds : 0 < l ∧ l ≤ tailLog ∧ tailLog ≤ u ∧ 0 ≤ crossLog ∧ crossLog ≤ w := by
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have hab : 1 ≤ beta/alpha := (le_div_iff₀ ha).2 (by simpa using fixed_geometry.2.2.1)
  have hbc : beta ≤ lam-alpha := by
    norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have hl := log_lower hab
  have hu := log_upper hab
  have hw := log_upper ((le_div_iff₀ hb).2 (by simpa using hbc))
  rw [log_div hb.ne' ha.ne'] at hl hu
  rw [log_div (hb.trans_le hbc).ne' hb.ne'] at hw
  refine ⟨?_,hl,hu,log_caps.2.2.1,hw⟩
  norm_num [l,lowerLog,alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- The negative fifth power is paid with the LOWER logarithmic envelope. -/
theorem I10_le_tenUpper : I10 ≤ tenUpper := by
  obtain ⟨hl0,hl,hu,_,_⟩ := fixed_log_bounds
  have hL0 := hl0.le.trans hl
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have hp := div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0 hu 4)
    (by positivity : 0 ≤ 24*alpha)
  have hn := div_le_div_of_nonneg_right (pow_le_pow_left₀ hl0.le hl 5)
    (by positivity : 0 ≤ 60*beta)
  exact I10_log_affine_upper.trans
    (mul_le_mul_of_nonneg_left (sub_le_sub hp hn) (by norm_num))

/-- First compare the brackets, including their negative fourth powers. -/
theorem eleven_bracket_upper :
    tailLog^3/(6*alpha)-tailLog^4/(12*beta) ≤ u^3/(6*alpha)-l^4/(12*beta) := by
  obtain ⟨hl0,hl,hu,_,_⟩ := fixed_log_bounds
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  exact sub_le_sub
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (hl0.le.trans hl) hu 3) (by positivity))
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hl0.le hl 4) (by positivity))

theorem rational_eleven_bracket_nonneg : 0 ≤ u^3/(6*alpha)-l^4/(12*beta) :=
  eleven_bracket_nonneg.trans eleven_bracket_upper

/-- Nonnegative actual and rational brackets justify payment of the upper cross logarithm. -/
theorem I11_le_elevenUpper : I11 ≤ elevenUpper := by
  obtain ⟨_,_,_,hW0,hW⟩ := fixed_log_bounds
  have hp := mul_le_mul hW eleven_bracket_upper eleven_bracket_nonneg (hW0.trans hW)
  have h := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4/7)
  unfold elevenUpper
  exact I11_log_affine_upper.trans (by simpa only [mul_assoc] using h)

theorem original_four_le_newFour : 8*I10+8*I11 ≤ newFour := by
  unfold newFour
  linarith [I10_le_tenUpper,I11_le_elevenUpper]

/-- The prescribed fixed payment succeeds in the kernel; no parameter or order search. -/
theorem newFour_lt_old : newFour < 21/20 := by
  norm_num [newFour,tenUpper,elevenUpper,l,u,w,lowerLog,upperLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

end Wu2008DoubleSieve.FourLogAffine
