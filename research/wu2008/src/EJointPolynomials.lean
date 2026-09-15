import F1OriginalEAssembly

noncomputable section

open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps

open scoped Interval

namespace EJoint

def A0 (t : ℝ) : ℝ := 24*t^1 + 24*t^2 + 8*t^3

def A1 (t : ℝ) : ℝ := 12*t^2 + 8*t^3 + 2*t^4

def A2 (t : ℝ) : ℝ := 4*t^3 + 2*t^4 + (2/5)*t^5

def A3 (t : ℝ) : ℝ := 1*t^4 + (2/5)*t^5 + (1/15)*t^6

def A4 (t : ℝ) : ℝ := (1/5)*t^5 + (1/15)*t^6 + (1/105)*t^7

def B0 (t : ℝ) : ℝ := 1152*t^1 + 3456*t^2 + 4416*t^3 + 3072*t^4 + 1224*t^5 + 264*t^6 + 24*t^7

def B1 (t : ℝ) : ℝ := 576*t^2 + 1152*t^3 + 1104*t^4 + (3072/5)*t^5 + 204*t^6 + (264/7)*t^7 + 3*t^8

def B2 (t : ℝ) : ℝ := 576*t^3 + 1008*t^4 + (4464/5)*t^5 + (2456/5)*t^6 + (876/5)*t^7 + (555/14)*t^8 + (109/21)*t^9 + (3/10)*t^10

def B3 (t : ℝ) : ℝ := 576*t^4 + (4608/5)*t^5 + (3816/5)*t^6 + (14288/35)*t^7 + 149*t^8 + (1298/35)*t^9 + (2537/420)*t^10 + (61/105)*t^11 + (1/40)*t^12

def B4 (t : ℝ) : ℝ := 576*t^5 + 864*t^6 + (3384/5)*t^7 + (12269/35)*t^8 + (40363/315)*t^9 + (2341/70)*t^10 + (28261/4620)*t^11 + (3757/5040)*t^12 + (593/10920)*t^13 + (1/560)*t^14

theorem A0_zero : A0 0 = 0 := by norm_num [A0]

theorem A0_continuous : Continuous A0 := by unfold A0; fun_prop

theorem A1_zero : A1 0 = 0 := by norm_num [A1]

theorem A1_continuous : Continuous A1 := by unfold A1; fun_prop

theorem A2_zero : A2 0 = 0 := by norm_num [A2]

theorem A2_continuous : Continuous A2 := by unfold A2; fun_prop

theorem A3_zero : A3 0 = 0 := by norm_num [A3]

theorem A3_continuous : Continuous A3 := by unfold A3; fun_prop

theorem A4_zero : A4 0 = 0 := by norm_num [A4]

theorem A4_continuous : Continuous A4 := by unfold A4; fun_prop

theorem B0_zero : B0 0 = 0 := by norm_num [B0]

theorem B0_continuous : Continuous B0 := by unfold B0; fun_prop

theorem B1_zero : B1 0 = 0 := by norm_num [B1]

theorem B1_continuous : Continuous B1 := by unfold B1; fun_prop

theorem B2_zero : B2 0 = 0 := by norm_num [B2]

theorem B2_continuous : Continuous B2 := by unfold B2; fun_prop

theorem B3_zero : B3 0 = 0 := by norm_num [B3]

theorem B3_continuous : Continuous B3 := by unfold B3; fun_prop

theorem B4_zero : B4 0 = 0 := by norm_num [B4]

theorem B4_continuous : Continuous B4 := by unfold B4; fun_prop

theorem A1_deriv (t : ℝ) : HasDerivAt A1 (A0 t) t := by

  have h := ((((hasDerivAt_pow 2 t).const_mul (12 : ℝ)).add ((hasDerivAt_pow 3 t).const_mul (8 : ℝ))).add ((hasDerivAt_pow 4 t).const_mul (2 : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [A0]
  ring

theorem A2_deriv (t : ℝ) : HasDerivAt A2 (A1 t) t := by

  have h := ((((hasDerivAt_pow 3 t).const_mul (4 : ℝ)).add ((hasDerivAt_pow 4 t).const_mul (2 : ℝ))).add ((hasDerivAt_pow 5 t).const_mul ((2/5) : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [A1]
  ring

theorem A3_deriv (t : ℝ) : HasDerivAt A3 (A2 t) t := by

  have h := ((((hasDerivAt_pow 4 t).const_mul (1 : ℝ)).add ((hasDerivAt_pow 5 t).const_mul ((2/5) : ℝ))).add ((hasDerivAt_pow 6 t).const_mul ((1/15) : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [A2]
  ring

theorem A4_deriv (t : ℝ) : HasDerivAt A4 (A3 t) t := by

  have h := ((((hasDerivAt_pow 5 t).const_mul ((1/5) : ℝ)).add ((hasDerivAt_pow 6 t).const_mul ((1/15) : ℝ))).add ((hasDerivAt_pow 7 t).const_mul ((1/105) : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [A3]
  ring

theorem B1_deriv (t : ℝ) : HasDerivAt B1 (B0 t) t := by

  have h := ((((((((hasDerivAt_pow 2 t).const_mul (576 : ℝ)).add ((hasDerivAt_pow 3 t).const_mul (1152 : ℝ))).add ((hasDerivAt_pow 4 t).const_mul (1104 : ℝ))).add ((hasDerivAt_pow 5 t).const_mul ((3072/5) : ℝ))).add ((hasDerivAt_pow 6 t).const_mul (204 : ℝ))).add ((hasDerivAt_pow 7 t).const_mul ((264/7) : ℝ))).add ((hasDerivAt_pow 8 t).const_mul (3 : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [B0]
  ring

theorem B2_deriv (t : ℝ) : HasDerivAt B2 ((t+3)*B1 t) t := by

  have h := (((((((((hasDerivAt_pow 3 t).const_mul (576 : ℝ)).add ((hasDerivAt_pow 4 t).const_mul (1008 : ℝ))).add ((hasDerivAt_pow 5 t).const_mul ((4464/5) : ℝ))).add ((hasDerivAt_pow 6 t).const_mul ((2456/5) : ℝ))).add ((hasDerivAt_pow 7 t).const_mul ((876/5) : ℝ))).add ((hasDerivAt_pow 8 t).const_mul ((555/14) : ℝ))).add ((hasDerivAt_pow 9 t).const_mul ((109/21) : ℝ))).add ((hasDerivAt_pow 10 t).const_mul ((3/10) : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [B1]
  ring

theorem B3_deriv (t : ℝ) : HasDerivAt B3 ((t+4)*B2 t) t := by

  have h := ((((((((((hasDerivAt_pow 4 t).const_mul (576 : ℝ)).add ((hasDerivAt_pow 5 t).const_mul ((4608/5) : ℝ))).add ((hasDerivAt_pow 6 t).const_mul ((3816/5) : ℝ))).add ((hasDerivAt_pow 7 t).const_mul ((14288/35) : ℝ))).add ((hasDerivAt_pow 8 t).const_mul (149 : ℝ))).add ((hasDerivAt_pow 9 t).const_mul ((1298/35) : ℝ))).add ((hasDerivAt_pow 10 t).const_mul ((2537/420) : ℝ))).add ((hasDerivAt_pow 11 t).const_mul ((61/105) : ℝ))).add ((hasDerivAt_pow 12 t).const_mul ((1/40) : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [B2]
  ring

theorem B4_deriv (t : ℝ) : HasDerivAt B4 ((t+5)*B3 t) t := by

  have h := (((((((((((hasDerivAt_pow 5 t).const_mul (576 : ℝ)).add ((hasDerivAt_pow 6 t).const_mul (864 : ℝ))).add ((hasDerivAt_pow 7 t).const_mul ((3384/5) : ℝ))).add ((hasDerivAt_pow 8 t).const_mul ((12269/35) : ℝ))).add ((hasDerivAt_pow 9 t).const_mul ((40363/315) : ℝ))).add ((hasDerivAt_pow 10 t).const_mul ((2341/70) : ℝ))).add ((hasDerivAt_pow 11 t).const_mul ((28261/4620) : ℝ))).add ((hasDerivAt_pow 12 t).const_mul ((3757/5040) : ℝ))).add ((hasDerivAt_pow 13 t).const_mul ((593/10920) : ℝ))).add ((hasDerivAt_pow 14 t).const_mul ((1/560) : ℝ)))

  convert h using 1 <;> first | rfl | skip
  norm_num [B3]
  ring

theorem numerator_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ A0 t := by unfold A0; positivity

theorem denominator_kernel (t : ℝ) : B0 t = 3*A0 t*(t+2)^4 := by unfold A0 B0; ring

end EJoint
