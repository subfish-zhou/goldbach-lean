import W13TightApi

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass WuTarget.W13

namespace WuTarget.W13Tight

def primitive (n : ℕ) (s : ℝ) : ℝ :=
  (h+s)^(n+2)/((n : ℝ)+2)-h*(h+s)^(n+1)/((n : ℝ)+1)

def discount (n : ℕ) : ℝ := primitive n d-primitive n 0

def discountDensity (n : ℕ) (x : ℝ) : ℝ :=
  (log cut-log x)*(h+(log cut-log x))^n/x

def momentUpper (n : ℕ) : ℝ :=
  8*FourLogAffine.u^(n+1)/((n : ℝ)+1)-8*k*discount n

theorem primitive_derivative (n : ℕ) (s : ℝ) :
    HasDerivAt (primitive n) (s*(h+s)^n) s := by
  have hg := (hasDerivAt_id s).const_add h
  have hp := ((hg.pow (n+2)).div_const ((n : ℝ)+2)).sub
    (((hg.pow (n+1)).const_mul h).div_const ((n : ℝ)+1))
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hp
  change HasDerivAt (primitive n)
    ((n+2 : ℝ)*(h+s)^(n+2-1)*1/((n : ℝ)+2)-
      h*((n+1 : ℝ)*(h+s)^(n+1-1)*1)/((n : ℝ)+1)) s at hp
  convert hp using 1
  simp only [show n+2-1 = n+1 by omega, Nat.add_sub_cancel, mul_one]
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp
  simp only [pow_succ]
  ring

theorem polynomial_integral (n : ℕ) (a b : ℝ) :
    (∫ s in a..b, s*(h+s)^n) = primitive n b-primitive n a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => primitive_derivative n s)
    ((by fun_prop : Continuous (fun s : ℝ => s*(h+s)^n)).intervalIntegrable a b)

theorem primitive_monotone (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    primitive n a ≤ primitive n b := by
  have hh := fixed_lower_logs.1
  have hi : 0 ≤ ∫ s in a..b, s*(h+s)^n :=
    intervalIntegral.integral_nonneg hab (fun s hs => by
      have hs0 := ha.trans hs.1
      positivity)
  rw [polynomial_integral] at hi
  linarith only [hi]

theorem density_integrable (n : ℕ) :
    IntervalIntegrable (discountDensity n) volume alpha cut := by
  have hx : ∀ x ∈ uIcc alpha cut, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le geometry.2.1] at hx
    exact (geometry.1.trans_le hx.1).ne'
  have hs : ContinuousOn (fun x => log cut-log x) (uIcc alpha cut) :=
    continuousOn_const.sub (continuousOn_id.log hx)
  exact ((hs.mul ((continuousOn_const.add hs).pow n)).div
    continuousOn_id hx).intervalIntegrable

theorem density_integral (n : ℕ) :
    (∫ x in alpha..cut, discountDensity n x) =
      primitive n (log cut-log alpha)-primitive n 0 := by
  have hd (x : ℝ) (hx : x ∈ uIcc alpha cut) :
      HasDerivAt (fun x => -primitive n (log cut-log x)) (discountDensity n x) x := by
    rw [uIcc_of_le geometry.2.1] at hx
    have hx0 := geometry.1.trans_le hx.1
    have hd := ((primitive_derivative n (log cut-log x)).comp x
      ((hasDerivAt_const x (log cut)).sub (hasDerivAt_log hx0.ne'))).neg
    convert hd using 1 <;> first | rfl | (unfold discountDensity; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (density_integrable n)]
  simp only [sub_self]
  ring

theorem density_payment (n : ℕ) :
    discount n ≤ ∫ x in alpha..cut, discountDensity n x := by
  rw [density_integral]
  have hp := primitive_monotone n fixed_lower_logs.2.2.1.le
    fixed_lower_logs.2.2.2.1
  unfold discount
  linarith only [hp]

theorem small_pointwise (n : ℕ) {x : ℝ} (hx : x ∈ Icc alpha cut) :
    (36/5)*(tail n x/(1-x))+8*k*discountDensity n x ≤ 8*tail n x := by
  have hx0 := geometry.1.trans_le hx.1
  have hs0 : 0 ≤ log cut-log x := sub_nonneg.mpr (log_le_log hx0 hx.2)
  have hl : h+(log cut-log x) ≤ log beta-log x := by
    linarith only [fixed_lower_logs.2.1]
  have hbase0 : 0 ≤ h+(log cut-log x) := by
    have hh := fixed_lower_logs.1
    positivity
  have hp := pow_le_pow_left₀ hbase0 hl n
  have ht0 : 0 ≤ tail n x := div_nonneg (pow_nonneg (hbase0.trans hl) _) hx0.le
  have h1 := mul_le_mul_of_nonneg_right (original_weight_discount hx) ht0
  have h2 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hx0.le)
    (mul_nonneg fixed_lower_logs.2.2.2.2.le hs0)
  have he : (36/5)*(tail n x/(1-x)) =
      8*tail n x-8*((cut-x)/(1-x))*tail n x := by
    have hn : 1-x ≠ 0 := by linarith [hx.2, geometry.2.2.2]
    unfold cut
    field_simp
    ring
  rw [he]
  dsimp only [tail, discountDensity] at h1 h2 ⊢
  ring_nf at h1 h2 ⊢
  linarith only [h1, h2]

theorem moment_upper (n : ℕ) : moment n ≤ momentUpper n := by
  have hc0 := geometry.1.trans_le geometry.2.1
  have hs := (tail_continuousOn n geometry.1 geometry.2.1).intervalIntegrable (μ := volume)
  have ht := (tail_continuousOn n hc0 geometry.2.2.1).intervalIntegrable (μ := volume)
  have hdI := (density_integrable n).const_mul (8*k)
  have hi := intervalIntegral.integral_mono_on geometry.2.1
    (((weighted_tail_integrable n).const_mul (36/5)).add hdI)
    (hs.const_mul 8) (fun x hx => small_pointwise n hx)
  rw [intervalIntegral.integral_add
    ((weighted_tail_integrable n).const_mul (36/5)) hdI] at hi
  simp only [intervalIntegral.integral_const_mul] at hi
  have hadj := intervalIntegral.integral_add_adjacent_intervals hs ht
  have hfull := ClassicalLogFourBounds.integral_log_tail
    (C := (1 : ℝ)) geometry.1 (geometry.2.1.trans geometry.2.2.1) n
  simp only [one_mul] at hfull
  change (∫ x in alpha..beta, tail n x) = _ at hfull
  rw [hfull] at hadj
  have hpay := mul_le_mul_of_nonneg_left (density_payment n)
    (show 0 ≤ 8*k from by have hk := fixed_lower_logs.2.2.2.2; positivity)
  have hu := pow_le_pow_left₀ ClassicalLogFourBounds.log_caps.1
    FourLogAffine.fixed_log_bounds.2.2.1 (n+1)
  have hupper := div_le_div_of_nonneg_right hu
    (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)
  unfold moment momentUpper
  unfold ClassicalLogFourBounds.tailLog at hupper
  ring_nf at hi hadj hpay hupper ⊢
  linarith only [hi, hadj, hpay, hupper]

theorem discount_two :
    discount 2 = h^2*d^2/2+2*h*d^3/3+d^4/4 := by
  unfold discount primitive
  norm_num
  ring

theorem discount_three :
    discount 3 = h^3*d^2/2+h^2*d^3+3*h*d^4/4+d^5/5 := by
  unfold discount primitive
  norm_num
  ring

theorem discount_four :
    discount 4 = h^4*d^2/2+4*h^3*d^3/3+3*h^2*d^4/2+4*h*d^5/5+d^6/6 := by
  unfold discount primitive
  norm_num
  ring

theorem discount_strict :
    h^2*d^2/2 < discount 2 ∧ h^3*d^2/2 < discount 3 ∧
      h^4*d^2/2 < discount 4 := by
  rw [discount_two, discount_three, discount_four]
  have hh := fixed_lower_logs.1
  have hd := fixed_lower_logs.2.2.1
  constructor
  · have hpos : 0 < 2*h*d^3/3+d^4/4 := by positivity
    linarith only [hpos]
  constructor
  · have hpos : 0 < h^2*d^3+3*h*d^4/4+d^5/5 := by positivity
    linarith only [hpos]
  · have hpos : 0 < 4*h^3*d^3/3+3*h^2*d^4/2+4*h*d^5/5+d^6/6 := by positivity
    linarith only [hpos]

end WuTarget.W13Tight
