import WR2ClassicalFourthTable

noncomputable section
namespace WuPaper.ClassicalIntegerPayments
open Real

/-- Integer table checks pay both trapezoid endpoints and the analytic cell error. -/
theorem direct_payment (a b u v E : ℕ)
    (h : 6*4000^3*u+3*4000^2*(a+b)+E*1000000000000000 ≤ 6*4000^3*v) :
    (1:ℝ)/4000*((a:ℝ)/1000000000000000+b/1000000000000000)/2+
      (E:ℝ)*((1:ℝ)/4000)^3/6 ≤ v/1000000000000000-u/1000000000000000 := by
  have hr : (6*4000^3:ℝ)*u+3*4000^2*(a+b)+(E:ℝ)*1000000000000000 ≤ 6*4000^3*v := by
    exact_mod_cast h
  norm_num at hr ⊢
  linarith only [hr]

/-- The C and D steps divide their input table by the moving recurrence parameter. -/
theorem divided_payment (m a b u v E : ℕ) (hm : 0 < m)
    (h : 6*4000^3*m*(m+1)*u+3*4000^3*((m+1)*a+m*b)+E*1000000000000000*m*(m+1) ≤
      6*4000^3*m*(m+1)*v) :
    (1:ℝ)/4000*(((a:ℝ)/1000000000000000)/((m:ℝ)/4000)+
      ((b:ℝ)/1000000000000000)/(((m:ℝ)+1)/4000))/2+
      (E:ℝ)*((1:ℝ)/4000)^3/6 ≤ v/1000000000000000-u/1000000000000000 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hr : (6*4000^3:ℝ)*m*(m+1)*u+3*4000^3*((m+1)*a+m*b)+(E:ℝ)*1000000000000000*m*(m+1) ≤
      6*4000^3*m*(m+1)*v := by exact_mod_cast h
  have hx := div_nonneg (sub_nonneg.mpr hr)
    (show (0:ℝ) ≤ 6*4000^3*1000000000000000*m*(m+1) by positivity)
  apply sub_nonneg.mp
  convert hx using 1 <;> solve | rfl | ring | (field_simp [hm0.ne',hm1.ne']; ring)

/-- The outer reciprocal weight has a positive integer denominator on the entire grid. -/
theorem outer_payment (m w a b q : ℕ) (hm : 0 < m) (hw : 0 < w)
    (h : 2654*4000^2*(1000000000000000+a+b) ≤ m*w*q) :
    (1+(a:ℝ)/1000000000000000+b/1000000000000000)/
      (((m:ℝ)/4000)*((w:ℝ)/(2654*4000))) ≤ q/1000000000000000 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hw0 : (0:ℝ) < w := by exact_mod_cast hw
  have hr : (2654*4000^2:ℝ)*(1000000000000000+a+b) ≤ (m:ℝ)*w*q := by exact_mod_cast h
  apply (div_le_iff₀ (by positivity : (0:ℝ) < ((m:ℝ)/4000)*((w:ℝ)/(2654*4000)))).mpr
  norm_num
  nlinarith only [hr]

end WuPaper.ClassicalIntegerPayments
#print axioms WuPaper.ClassicalIntegerPayments.direct_payment
#print axioms WuPaper.ClassicalIntegerPayments.divided_payment
#print axioms WuPaper.ClassicalIntegerPayments.outer_payment
