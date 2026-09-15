import W13Api

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass SharpLogRecurrence

namespace WuTarget.W13

def cut : ℝ := 1/10
def h : ℝ := lowerLog (beta/cut)
def d : ℝ := lowerLog (cut/alpha)
def k : ℝ := alpha/(1-alpha)

def tail (n : ℕ) (x : ℝ) : ℝ := (log beta-log x)^n/x

def moment (n : ℕ) : ℝ :=
  (36/5)*(∫ x in alpha..cut, tail n x/(1-x))+
    8*(∫ x in cut..beta, tail n x)

def momentUpper (n : ℕ) : ℝ :=
  8*FourLogAffine.u^(n+1)/(n+1)-8*k*h^n*d^2/2

theorem geometry :
    0 < alpha ∧ alpha ≤ cut ∧ cut ≤ beta ∧ cut < 1 := by
  norm_num [alpha, beta, cut, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem fixed_lower_logs :
    0 < h ∧ h ≤ log beta-log cut ∧
    0 < d ∧ d ≤ log cut-log alpha ∧ 0 < k := by
  have hc : 0 < cut := geometry.1.trans_le geometry.2.1
  have hb : 0 < beta := hc.trans_le geometry.2.2.1
  have hh := log_lower ((le_div_iff₀ hc).mpr (by simpa using geometry.2.2.1))
  have hd := log_lower ((le_div_iff₀ geometry.1).mpr (by simpa using geometry.2.1))
  rw [log_div hb.ne' hc.ne'] at hh
  rw [log_div hc.ne' geometry.1.ne'] at hd
  refine ⟨?_, hh, ?_, hd, ?_⟩ <;>
    norm_num [h, d, k, lowerLog, cut, alpha, beta,
      truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem tail_continuousOn (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (tail n) (uIcc a b) := by
  have hx : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (ha.trans_le hx.1).ne'
  exact ((continuousOn_const.sub (continuousOn_id.log hx)).pow n).div
    continuousOn_id hx

theorem weighted_tail_integrable (n : ℕ) :
    IntervalIntegrable (fun x => tail n x/(1-x)) volume alpha cut := by
  apply ContinuousOn.intervalIntegrable
  apply (tail_continuousOn n geometry.1 geometry.2.1).div (by fun_prop)
  intro x hx
  rw [uIcc_of_le geometry.2.1] at hx
  linarith [hx.2, geometry.2.2.2]

theorem original_weight_discount {x : ℝ} (hx : x ∈ Icc alpha cut) :
    k*(log cut-log x) ≤ (cut-x)/(1-x) := by
  have hx0 := geometry.1.trans_le hx.1
  have hc0 := hx0.trans_le hx.2
  have hax : 0 < 1-alpha := by linarith [geometry.2.1, geometry.2.2.2]
  have hxx : 0 < 1-x := by linarith [hx.2, geometry.2.2.2]
  have hl0 : 0 ≤ log cut-log x := sub_nonneg.mpr (log_le_log hx0 hx.2)
  have hl : log cut-log x ≤ (cut-x)/x := by
    have hh := log_le_sub_one_of_pos (div_pos hc0 hx0)
    rw [log_div hc0.ne' hx0.ne'] at hh
    convert hh using 1
    field_simp
  have hk : k ≤ x/(1-x) := by
    unfold k
    apply (div_le_div_iff₀ hax hxx).mpr
    nlinarith only [hx.1]
  calc
    _ ≤ (x/(1-x))*(log cut-log x) := mul_le_mul_of_nonneg_right hk hl0
    _ ≤ (x/(1-x))*((cut-x)/x) :=
      mul_le_mul_of_nonneg_left hl (div_nonneg hx0.le hxx.le)
    _ = _ := by field_simp

theorem small_pointwise (n : ℕ) {x : ℝ} (hx : x ∈ Icc alpha cut) :
    (36/5)*(tail n x/(1-x))+
      (8*k*h^n)*(log cut-log x)/x ≤ 8*tail n x := by
  have hx0 := geometry.1.trans_le hx.1
  have hl0 : 0 ≤ log cut-log x := sub_nonneg.mpr (log_le_log hx0 hx.2)
  have hh : h ≤ log beta-log x :=
    fixed_lower_logs.2.1.trans (by linarith only [hl0])
  have hhpow := pow_le_pow_left₀ fixed_lower_logs.1.le hh n
  have htail0 : 0 ≤ tail n x :=
    div_nonneg (pow_nonneg (fixed_lower_logs.1.le.trans hh) n) hx0.le
  have h1 := mul_le_mul_of_nonneg_right (original_weight_discount hx) htail0
  have h2 := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hhpow hx0.le)
    (mul_nonneg fixed_lower_logs.2.2.2.2.le hl0)
  have he : (36/5)*(tail n x/(1-x)) =
      8*tail n x-8*((cut-x)/(1-x))*tail n x := by
    have hn : 1-x ≠ 0 := by linarith [hx.2, geometry.2.2.2]
    unfold cut
    field_simp
    ring
  rw [he]
  dsimp only [tail] at h1 h2 ⊢
  ring_nf at h1 h2 ⊢
  linarith only [h1, h2]

theorem moment_upper (n : ℕ) : moment n ≤ momentUpper n := by
  have hc0 := geometry.1.trans_le geometry.2.1
  have hs := (tail_continuousOn n geometry.1 geometry.2.1).intervalIntegrable (μ := volume)
  have ht := (tail_continuousOn n hc0 geometry.2.2.1).intervalIntegrable (μ := volume)
  have hdI := FourLogAffine.tail_integrable
    (C := 8*k*h^n) geometry.1 geometry.2.1 1
  have hi := intervalIntegral.integral_mono_on geometry.2.1
    ((weighted_tail_integrable n).const_mul (36/5) |>.add hdI)
    (hs.const_mul 8) (fun x hx => by
      simpa only [pow_one] using small_pointwise n hx)
  rw [intervalIntegral.integral_add
    ((weighted_tail_integrable n).const_mul (36/5)) hdI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ClassicalLogFourBounds.integral_log_tail geometry.1 geometry.2.1 1] at hi
  have hadj := intervalIntegral.integral_add_adjacent_intervals hs ht
  have hfull := ClassicalLogFourBounds.integral_log_tail
    (C := (1 : ℝ)) geometry.1 (geometry.2.1.trans geometry.2.2.1) n
  simp only [one_mul] at hfull
  change (∫ x in alpha..beta, tail n x) = _ at hfull
  have hdpow := pow_le_pow_left₀ fixed_lower_logs.2.2.1.le
    fixed_lower_logs.2.2.2.1 2
  have hpay := mul_le_mul_of_nonneg_left hdpow
    (show 0 ≤ 8*k*h^n from by
      have hk := fixed_lower_logs.2.2.2.2
      have hh := fixed_lower_logs.1
      positivity)
  have hu := pow_le_pow_left₀ ClassicalLogFourBounds.log_caps.1
    FourLogAffine.fixed_log_bounds.2.2.1 (n+1)
  have hupper := div_le_div_of_nonneg_right hu
    (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)
  unfold moment momentUpper
  unfold ClassicalLogFourBounds.tailLog at hupper
  norm_num only [Nat.cast_one, one_add_one_eq_two] at hi
  rw [hfull] at hadj
  ring_nf at hi hadj hpay hupper ⊢
  linarith only [hi, hadj, hpay, hupper]

end WuTarget.W13
