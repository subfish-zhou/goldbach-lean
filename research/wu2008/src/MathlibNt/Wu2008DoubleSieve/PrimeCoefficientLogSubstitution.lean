import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Logarithmic substitution for possibly discontinuous sieve coefficients

Wu04, original TeX lines 1101--1106. The Jacobian theorem used below places
no continuity requirement on the integrand. Only the logarithmic coordinate
map is differentiated. Monotonicity supplies integrability separately.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

private theorem logCoordinate_data {q a b : ℝ}
    (hq : 1 < q) (ha : 1 < a) :
    ContinuousOn (fun x => log q / log x - 1) (Icc a b) ∧
      AntitoneOn (fun x => log q / log x - 1) (Icc a b) ∧
      ∀ x ∈ Icc a b, HasDerivWithinAt (fun y => log q / log y - 1)
        (-(log q / (x * (log x) ^ 2))) (Icc a b) x := by
  have hlog (x : ℝ) (hx : x ∈ Icc a b) : 0 < log x :=
    log_pos (ha.trans_le hx.1)
  refine ⟨?_, ?_, ?_⟩
  · exact (continuousOn_const.div
      (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
      (fun x hx => (hlog x hx).ne')).sub continuousOn_const
  · intro x hx y hy hxy
    exact sub_le_sub_right (div_le_div_of_nonneg_left (log_pos hq).le
      (hlog x hx) (log_le_log (by linarith [hx.1]) hxy)) 1
  · intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hd := ((hasDerivAt_const x (log q)).div (hasDerivAt_log hx0)
      (hlog x hx).ne').sub_const 1
    have heq : (0 * log x - log q * x⁻¹) / (log x) ^ 2 =
        -(log q / (x * (log x) ^ 2)) := by
      field_simp
      ring
    rw [heq] at hd
    exact hd.hasDerivWithinAt

private theorem logCoordinate_half {q a b x : ℝ}
    (hq : 1 < q) (ha : 1 < a) (hx : x ∈ Icc a b)
    (hb : b ≤ q ^ (1 / 2 : ℝ)) :
    0 < log x ∧ 1 ≤ log q / log x - 1 ∧ 0 < 1 - log x / log q := by
  have hlx : 0 < log x := log_pos (ha.trans_le hx.1)
  have hlq : 0 < log q := log_pos hq
  have hh := log_le_log (by linarith [hx.1] : 0 < x) (hx.2.trans hb)
  rw [log_rpow (by linarith : 0 < q)] at hh
  have h2 : 2 ≤ log q / log x := (le_div_iff₀ hlx).2 (by linarith)
  have hhalf : log x / log q ≤ 1 / 2 := (div_le_iff₀ hlq).2 (by linarith)
  exact ⟨hlx, by linarith, by linarith⟩

private theorem logCoordinate_jacobian {f : ℝ → ℝ} {q a b x : ℝ}
    (hq : 1 < q) (ha : 1 < a) (hx : x ∈ Icc a b)
    (hb : b ≤ q ^ (1 / 2 : ℝ)) :
    -(-(log q / (x * (log x) ^ 2))) •
        (f (log q / log x - 1) / (log q / log x - 1)) =
      f (log q / log x - 1) / (x * (1 - log x / log q) * log x) := by
  have hh := logCoordinate_half hq ha hx hb
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hu0 : log q - log x ≠ 0 := by
    have hlt : log x < log q := (div_lt_one (log_pos hq)).mp
      (show log x / log q < 1 by linarith [hh.2.2])
    linarith
  simp only [neg_neg, smul_eq_mul]
  field_simp [hx0, (log_pos hq).ne', hh.1.ne', hu0]

/-- Exact logarithmic substitution. No regularity assumption on `f` is
needed for the equality of Bochner integrals; integrability for the intended
bounded-monotone coefficients is proved separately below. -/
theorem wuPrime_log_substitution {f : ℝ → ℝ} {q a b : ℝ}
    (hq : 1 < q) (ha : 1 < a) (hab : a ≤ b)
    (hb : b ≤ q ^ (1 / 2 : ℝ)) :
    (∫ x in a..b,
      f (log q / log x - 1) / (x * (1 - log x / log q) * log x)) =
      ∫ u in (log q / log b - 1)..(log q / log a - 1), f u / u := by
  obtain ⟨hc, hm, hd⟩ := logCoordinate_data (b := b) hq ha
  have huv := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hchange := integral_image_eq_integral_deriv_smul_of_antitoneOn
    measurableSet_Icc hd hm (fun u => f u / u)
  rw [hc.image_Icc_of_antitoneOn hab hm] at hchange
  rw [intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le huv,
    ← integral_Icc_eq_integral_Ioc, hchange]
  exact (setIntegral_congr_fun measurableSet_Icc
    (fun x hx => logCoordinate_jacobian hq ha hx hb)).symm

/-- Both sides of logarithmic substitution are integrable for monotone,
possibly signed or discontinuous `f`. The argument bounds hold on the
whole continuous interval, including both endpoints. -/
theorem wuPrime_log_intervalIntegrable {f : ℝ → ℝ} {q a b : ℝ}
    (hf : MonotoneOn f (Icc 1 10)) (hq : 1 < q)
    (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log a - 1 ≤ 10) :
    IntervalIntegrable (fun u => f u / u) volume
        (log q / log b - 1) (log q / log a - 1) ∧
      IntervalIntegrable (fun x =>
        f (log q / log x - 1) / (x * (1 - log x / log q) * log x))
        volume a b := by
  obtain ⟨hc, hm, hd⟩ := logCoordinate_data (b := b) hq ha
  have huv := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hub := (logCoordinate_half hq ha (right_mem_Icc.mpr hab) hb).2.1
  have hs : uIcc (log q / log b - 1) (log q / log a - 1) ⊆ Icc (1 : ℝ) 10 := by
    rw [uIcc_of_le huv]
    exact Icc_subset_Icc hub haq
  have hfi := (hf.mono hs).intervalIntegrable (μ := volume)
  have hinv : ContinuousOn (fun u : ℝ => u⁻¹)
      (uIcc (log q / log b - 1) (log q / log a - 1)) :=
    continuousOn_id.inv₀ (fun u hu => by change u ≠ 0; linarith [(hs hu).1])
  have hi : IntervalIntegrable (fun u => f u / u) volume
      (log q / log b - 1) (log q / log a - 1) := by
    simpa only [div_eq_mul_inv] using hfi.mul_continuousOn hinv
  refine ⟨hi, ?_⟩
  have himage : IntegrableOn (fun u => f u / u)
      ((fun x => log q / log x - 1) '' Icc a b) := by
    rw [hc.image_Icc_of_antitoneOn hab hm]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hi
  have hj := (integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
    measurableSet_Icc hd hm (fun u => f u / u)).mp himage
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact hj.congr_fun (fun x hx => logCoordinate_jacobian hq ha hx hb) measurableSet_Icc

private theorem shiftedKernel_pointwise {f : ℝ → ℝ} {q a b B x : ℝ}
    (hq : 1 < q) (ha : 4 ≤ a) (hx : x ∈ Icc a b)
    (hb : b ≤ q ^ (1 / 2 : ℝ)) (hB : 0 ≤ B)
    (hfx : |f (log q / log x - 1)| ≤ B) :
    |f (log q / log x - 1) / ((x - 2) * (1 - log x / log q) * log x) -
      f (log q / log x - 1) / (x * (1 - log x / log q) * log x)| ≤
      (8 * B / log a) * (x ^ 2)⁻¹ := by
  have hx4 : 4 ≤ x := ha.trans hx.1
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 2 := by linarith
  have hla : 0 < log a := log_pos (by linarith)
  have hlx : 0 < log x := log_pos (by linarith)
  have hlq : 0 < log q := log_pos hq
  have hlogs := log_le_log (by linarith : 0 < a) hx.1
  have hqbound := log_le_log hx0 (hx.2.trans hb)
  rw [log_rpow (by linarith : 0 < q)] at hqbound
  have hc : 1 / 2 ≤ 1 - log x / log q := by
    have hh : log x / log q ≤ 1 / 2 := (div_le_iff₀ hlq).2 (by linarith)
    linarith
  have hc0 : 0 < 1 - log x / log q := by linarith
  have heq :
      f (log q / log x - 1) / ((x - 2) * (1 - log x / log q) * log x) -
        f (log q / log x - 1) / (x * (1 - log x / log q) * log x) =
      2 * f (log q / log x - 1) /
        ((x - 2) * x * (1 - log x / log q) * log x) := by
    field_simp
    ring
  rw [heq, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (mul_pos (mul_pos (mul_pos hxm hx0) hc0) hlx)]
  have hden : (x / 2) * x * (1 / 2) * log a ≤
      (x - 2) * x * (1 - log x / log q) * log x := by
    gcongr
    linarith
  have hden0 : 0 < (x - 2) * x * (1 - log x / log q) * log x := by positivity
  calc
    _ ≤ 2 * B / ((x - 2) * x * (1 - log x / log q) * log x) := by
      gcongr
    _ ≤ (8 * B / log a) * (x ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_div]
      apply (div_le_div_iff₀ hden0 (mul_pos hla (sq_pos_of_pos hx0))).2
      nlinarith [mul_le_mul_of_nonneg_left hden hB]

private theorem integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (x ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hx0 (x : ℝ) (hx : x ∈ uIcc a b) : x ≠ 0 := by
    rw [uIcc_of_le hab] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (uIcc a b) :=
    (continuousOn_id.pow 2).inv₀ (fun x hx => pow_ne_zero 2 (hx0 x hx))
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    have hd0 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
      hasDerivAt_inv (hx0 x hx)
    simpa only [neg_neg] using! hd0.neg
  simpa only [neg_sub_neg] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- Explicit continuous `p-2` to `p` kernel payment, followed by the exact
logarithmic substitution. Uniform over signed bounded-monotone coefficients
and independent of the right endpoint. -/
theorem wuPrime_log_kernel_error {f : ℝ → ℝ} {q a b B : ℝ}
    (hf : MonotoneOn f (Icc 1 10)) (hq : 1 < q)
    (ha : 4 ≤ a) (hab : a ≤ b) (hb : b ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log a - 1 ≤ 10) (hB : 0 ≤ B)
    (hfb : ∀ u ∈ Icc (1 : ℝ) 10, |f u| ≤ B) :
    |(∫ x in a..b,
        f (log q / log x - 1) / ((x - 2) * (1 - log x / log q) * log x)) -
      ∫ u in (log q / log b - 1)..(log q / log a - 1), f u / u| ≤
        8 * B / a / log a := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hla : 0 < log a := log_pos ha1
  let F : ℝ → ℝ := fun x =>
    f (log q / log x - 1) / (x * (1 - log x / log q) * log x)
  let G : ℝ → ℝ := fun x =>
    f (log q / log x - 1) / ((x - 2) * (1 - log x / log q) * log x)
  have hFi : IntervalIntegrable F volume a b :=
    (wuPrime_log_intervalIntegrable hf hq ha1 hab hb haq).2
  have hGi : IntervalIntegrable G volume a b := by
    simpa only [G, wuPrimeRealWeight, div_div] using
      wuPrimeRealWeight_intervalIntegrable hf hq ha hab hb haq
  have hmajor : IntervalIntegrable (fun x : ℝ => (8 * B / log a) * (x ^ 2)⁻¹)
      volume a b := by
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_id.pow 2).inv₀
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact pow_ne_zero 2 (by change x ≠ 0; linarith [hx.1])
  rw [← wuPrime_log_substitution (f := f) hq ha1 hab hb]
  change |(∫ x in a..b, G x) - ∫ x in a..b, F x| ≤ _
  rw [← intervalIntegral.integral_sub hGi hFi]
  calc
    _ ≤ ∫ x in a..b, |G x - F x| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a..b, (8 * B / log a) * (x ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hab (hGi.sub hFi).abs hmajor
      intro x hx
      apply shiftedKernel_pointwise hq ha hx hb hB
      apply hfb
      refine ⟨(logCoordinate_half hq ha1 hx hb).2.1, ?_⟩
      exact (logCoordinate_data (b := b) hq ha1).2.1
        (left_mem_Icc.mpr hab) hx hx.1 |>.trans haq
    _ = (8 * B / log a) * (a⁻¹ - b⁻¹) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_sq ha0 hab]
    _ ≤ (8 * B / log a) * a⁻¹ :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr hb0.le)) (by positivity)
    _ = _ := by ring

/-- The kernel payment stated using the actual continuous prime weight. -/
theorem wuPrimeRealWeight_log_error {f : ℝ → ℝ} {q a b B : ℝ}
    (hf : MonotoneOn f (Icc 1 10)) (hq : 1 < q)
    (ha : 4 ≤ a) (hab : a ≤ b) (hb : b ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log a - 1 ≤ 10) (hB : 0 ≤ B)
    (hfb : ∀ u ∈ Icc (1 : ℝ) 10, |f u| ≤ B) :
    |(∫ x in a..b, wuPrimeRealWeight f q x / log x) -
      ∫ u in (log q / log b - 1)..(log q / log a - 1), f u / u| ≤
        8 * B / a / log a := by
  simpa only [wuPrimeRealWeight, div_div] using
    wuPrime_log_kernel_error hf hq ha hab hb haq hB hfb

open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The true-li RIGHT-sampled sum is now compared with the source `/u`
integral, consuming the actual continuous quadrature and its kernel payment. -/
theorem primeCoefficient_trueLi_to_log_integral
    {f : ℝ → ℝ} {q B : ℝ} (hf : MonotoneOn f (Icc 1 10))
    (hB : 0 ≤ B) (hfb : ∀ u ∈ Icc (1 : ℝ) 10, |f u| ≤ B)
    {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) (hq : 1 < q) (hlq : 2 ≤ log q)
    (hb : (b : ℝ) ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log (a : ℝ) - 1 ≤ 10) :
    |(∑ n ∈ Finset.Ico a b,
        (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
          wuPrimeCoefficientWeight f q (n + 1)) -
      ∫ u in (log q / log b - 1)..(log q / log a - 1), f u / u| ≤
        20 * B / (a : ℝ) / log a := by
  have hsample := primeCoefficient_trueLi_to_continuous hf hB hfb ha hab hq hlq hb haq
  have hkernel := wuPrimeRealWeight_log_error hf hq
    (by exact_mod_cast ha : (4 : ℝ) ≤ a) (by exact_mod_cast hab : (a : ℝ) ≤ b)
    hb haq hB hfb
  calc
    _ ≤ |(∑ n ∈ Finset.Ico a b,
          (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
            wuPrimeCoefficientWeight f q (n + 1)) -
          ∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x| +
        |(∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x) -
          ∫ u in (log q / log b - 1)..(log q / log a - 1), f u / u| :=
      abs_sub_le _ _ _
    _ ≤ 12 * B / (a : ℝ) / log a + 8 * B / (a : ℝ) / log a :=
      add_le_add hsample hkernel
    _ = _ := by ring

end Wu2008DoubleSieve
