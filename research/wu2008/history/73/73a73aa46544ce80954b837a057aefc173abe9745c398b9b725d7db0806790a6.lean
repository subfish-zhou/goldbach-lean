import MathlibNt.Wu2008DoubleSieve.PositiveGainActual

#check @Wu2008DoubleSieve.positiveGain_kernel_le
#print axioms Wu2008DoubleSieve.positiveGain_kernel_le
#check @Wu2008DoubleSieve.positiveGain_integral_le_simplex
#print axioms Wu2008DoubleSieve.positiveGain_integral_le_simplex
#check @Wu2008DoubleSieve.positiveGain_envelope_le_simplex
#print axioms Wu2008DoubleSieve.positiveGain_envelope_le_simplex
#check @Wu2008DoubleSieve.positiveGain_explicit_seed
#print axioms Wu2008DoubleSieve.positiveGain_explicit_seed
#check @Wu2008DoubleSieve.positiveGain_actual_upper_seed
#print axioms Wu2008DoubleSieve.positiveGain_actual_upper_seed
#check @Wu2008DoubleSieve.positiveGain_actual_upper_range
#print axioms Wu2008DoubleSieve.positiveGain_actual_upper_range
#check @Wu2008DoubleSieve.positiveGain_actual_lower_range
#print axioms Wu2008DoubleSieve.positiveGain_actual_lower_range

example {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (19/145000 : ℝ) ≤ Wu2008DoubleSieve.wuImprovementLimit false δ 2 := by
  have h := Wu2008DoubleSieve.positiveGain_actual_lower_range hδ hδhi
    (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 39/10)
  norm_num at h
  exact h

example : (2 : ℝ) ≤ 29/10 ∧ (29/10 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 31/10 ∧
    (31/10 : ℝ) ≤ 5 ∧ (2 : ℝ) ≤ 31/10-(31/10)/(29/10) := by norm_num
