import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralGlobal

/-!
# Right-sampled true-li quadrature for discontinuous coefficients

The error on each unit cell is paid by the oscillations of two antitone
factors. Their sum telescopes, so the bound is uniform over the entire
bounded-monotone class and does not involve the interval length.
This is the continuous-quadrature step in Wu04, following (3.15).
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

private theorem sum_real_forward_sub (u : ℝ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (u n - u (n + 1)) = u a - u b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    push_cast
    ring

/-- A right-endpoint quadrature bound for a signed antitone factor times
a continuous positive antitone kernel, against a bounded positive density.
The coefficient need not be continuous. -/
theorem antitone_product_right_quadrature
    {u v ρ : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b)
    (hu : AntitoneOn u (Set.Icc (a : ℝ) b))
    (hv : AntitoneOn v (Set.Icc (a : ℝ) b))
    (hvc : ContinuousOn v (Set.Icc (a : ℝ) b))
    (hρc : ContinuousOn ρ (Set.Icc (a : ℝ) b))
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hub : ∀ x ∈ Set.Icc (a : ℝ) b, |u x| ≤ B)
    (hv0 : ∀ x ∈ Set.Icc (a : ℝ) b, 0 ≤ v x)
    (hρ : ∀ x ∈ Set.Icc (a : ℝ) b, 0 ≤ ρ x ∧ ρ x ≤ R) :
    |(∑ n ∈ Finset.Ico a b,
        (∫ x in (n : ℝ)..(n + 1 : ℕ), ρ x) * (u (n + 1) * v (n + 1))) -
      ∫ x in (a : ℝ)..b, u x * v x * ρ x| ≤ 3 * B * v a * R := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hui : IntervalIntegrable u volume (a : ℝ) b := by
    apply AntitoneOn.intervalIntegrable
    simpa only [uIcc_of_le habR] using hu
  have hvi : ContinuousOn v (uIcc (a : ℝ) b) := by
    simpa only [uIcc_of_le habR] using hvc
  have hρi : ContinuousOn ρ (uIcc (a : ℝ) b) := by
    simpa only [uIcc_of_le habR] using hρc
  have hi := (hui.mul_continuousOn hvi).mul_continuousOn hρi
  have hcell (n : ℕ) (hn : n ∈ Finset.Ico a b) :
      uIcc (n : ℝ) (n + 1 : ℕ) ⊆ Icc (a : ℝ) b := by
    rw [Set.uIcc_of_le (by exact_mod_cast (show n ≤ n + 1 by omega))]
    exact Icc_subset_Icc (by exact_mod_cast (mem_Ico.mp hn).1)
      (by exact_mod_cast (show n + 1 ≤ b by have := mem_Ico.mp hn; omega))
  have hlocal (n : ℕ) (hn : n ∈ Finset.Ico a b) :
      |(∫ x in (n : ℝ)..(n + 1 : ℕ), ρ x) * (u (n + 1) * v (n + 1)) -
        ∫ x in (n : ℝ)..(n + 1 : ℕ), u x * v x * ρ x| ≤
      (v a * (u n - u (n + 1)) + B * (v n - v (n + 1))) * R := by
    have hnR : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.le_succ n)
    have hn0 := hcell n hn (left_mem_uIcc : (n : ℝ) ∈ uIcc (n : ℝ) (n + 1 : ℕ))
    have hn1 := hcell n hn (right_mem_uIcc : ((n + 1 : ℕ) : ℝ) ∈
      uIcc (n : ℝ) (n + 1 : ℕ))
    have hsub : uIcc (n : ℝ) (n + 1 : ℕ) ⊆ uIcc (a : ℝ) b := by
      simpa only [uIcc_of_le habR] using hcell n hn
    have hρni : IntervalIntegrable ρ volume (n : ℝ) (n + 1 : ℕ) :=
      (hρi.mono hsub).intervalIntegrable
    have hni := hi.mono_set hsub
    rw [← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_sub (hρni.mul_const _) hni]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (n : ℝ)) (b := (n + 1 : ℕ))
      (C := (v a * (u n - u (n + 1)) + B * (v n - v (n + 1))) * R)
      (f := fun x => ρ x * (u (n + 1) * v (n + 1)) - u x * v x * ρ x) ?_
    · simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
        add_sub_cancel_left, abs_one, mul_one] using hbound
    intro x hx
    have hx' : (n : ℝ) ≤ x ∧ x ≤ (n + 1 : ℕ) := by
      rw [uIoc_of_le hnR] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hx0 := hcell n hn (by rw [uIcc_of_le hnR]; exact hx')
    have hunx := hu hn0 hx0 hx'.1
    have hux1 := hu hx0 hn1 hx'.2
    have hvnx := hv hn0 hx0 hx'.1
    have hvx1 := hv hx0 hn1 hx'.2
    have hva1 := hv ⟨le_rfl, habR⟩ hn1 hn1.1
    push_cast at hn1 hux1 hvx1 hva1
    have huv :
        |u (n + 1) * v (n + 1) - u x * v x| ≤
          v a * (u n - u (n + 1)) + B * (v n - v (n + 1)) := by
      have heq : u (n + 1) * v (n + 1) - u x * v x =
          (u (n + 1) - u x) * v (n + 1) + u x * (v (n + 1) - v x) := by ring
      rw [heq]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg (hv0 _ hn1),
        abs_of_nonpos (sub_nonpos.mpr hux1),
        abs_of_nonpos (sub_nonpos.mpr hvx1)]
      have h1 := mul_le_mul (show u x - u (n + 1) ≤ u n - u (n + 1) by linarith)
        hva1 (hv0 _ hn1) (show 0 ≤ u n - u (n + 1) by linarith)
      have h2 := mul_le_mul (hub x hx0)
        (show v x - v (n + 1) ≤ v n - v (n + 1) by linarith)
        (sub_nonneg.mpr hvx1) hB
      nlinarith only [h1, h2]
    rw [Real.norm_eq_abs,
      show ρ x * (u (n + 1) * v (n + 1)) - u x * v x * ρ x =
        (u (n + 1) * v (n + 1) - u x * v x) * ρ x by ring,
      abs_mul, abs_of_nonneg (hρ x hx0).1]
    exact mul_le_mul huv (hρ x hx0).2 (hρ x hx0).1 (le_trans (abs_nonneg _) huv)
  have hsumint :
      ∑ n ∈ Finset.Ico a b, ∫ x in (n : ℝ)..(n + 1 : ℕ), u x * v x * ρ x =
        ∫ x in (a : ℝ)..b, u x * v x * ρ x := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico hab
    intro n hn
    apply hi.mono_set
    simpa only [uIcc_of_le habR] using hcell n (Finset.mem_Ico.mpr hn)
  rw [← hsumint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Ico a b,
        |(∫ x in (n : ℝ)..(n + 1 : ℕ), ρ x) * (u (n + 1) * v (n + 1)) -
          ∫ x in (n : ℝ)..(n + 1 : ℕ), u x * v x * ρ x| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ico a b,
        (v a * (u n - u (n + 1)) + B * (v n - v (n + 1))) * R :=
      Finset.sum_le_sum hlocal
    _ = (v a * (u a - u b) + B * (v a - v b)) * R := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        sum_real_forward_sub u hab, sum_real_forward_sub v hab]
    _ ≤ _ := by
      have hua := (abs_le.mp (hub _ ⟨le_rfl, habR⟩)).2
      have hub' := (abs_le.mp (hub _ ⟨habR, le_rfl⟩)).1
      have hva := hv0 _ ⟨le_rfl, habR⟩
      have hvb := hv0 _ ⟨habR, le_rfl⟩
      have h1 : v a * (u a - u b) ≤ 2 * B * v a := by nlinarith
      have h2 : B * (v a - v b) ≤ B * v a := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right (add_le_add h1 h2) hR]

noncomputable def wuPrimeRealWeight (f : ℝ → ℝ) (q x : ℝ) : ℝ :=
  f (log q / log x - 1) / ((x - 2) * (1 - log x / log q))

/-- The domain is checked on the entire continuous interval, starting at
`a`, not merely at the first sampled prime `a+1`. -/
theorem wuPrime_continuous_argument_mem {q a b x : ℝ}
    (hq : 1 < q) (ha : 1 < a) (hx : x ∈ Set.Icc a b)
    (hb : b ≤ q ^ (1 / 2 : ℝ)) (haq : log q / log a - 1 ≤ 10) :
    log q / log x - 1 ∈ Set.Icc (1 : ℝ) 10 := by
  have hxa : 1 < x := ha.trans_le hx.1
  have hlogx : 0 < log x := log_pos hxa
  have hlog := log_le_log (by linarith : 0 < x) (hx.2.trans hb)
  rw [log_rpow (by linarith : 0 < q)] at hlog
  constructor
  · have h := (le_div_iff₀ hlogx).2 (by linarith : 2 * log x ≤ log q)
    linarith
  · apply le_trans _ haq
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left (log_pos hq).le (log_pos ha)
        (log_le_log (by linarith) hx.1)) 1

theorem wuPrimeRealWeight_intervalIntegrable {f : ℝ → ℝ} {q a b : ℝ}
    (hf : MonotoneOn f (Set.Icc 1 10)) (hq : 1 < q)
    (ha : 4 ≤ a) (hab : a ≤ b) (hb : b ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log a - 1 ≤ 10) :
    IntervalIntegrable (fun x => wuPrimeRealWeight f q x / log x) volume a b := by
  have hdomain (x : ℝ) (hx : x ∈ Set.Icc a b) :=
    wuPrime_continuous_argument_mem hq (by linarith : 1 < a) hx hb haq
  have hu : AntitoneOn (fun x => f (log q / log x - 1)) (Set.Icc a b) := by
    intro x hx y hy hxy
    apply hf (hdomain y hy) (hdomain x hx)
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left (log_pos hq).le
        (log_pos (by linarith [hx.1])) (log_le_log (by linarith [hx.1]) hxy)) 1
  have hlogc : ContinuousOn (fun x : ℝ => log x) (Set.Icc a b) :=
    continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1])
  have hden (x : ℝ) (hx : x ∈ Set.Icc a b) :
      (x - 2) * (1 - log x / log q) ≠ 0 := by
    have hh := reboxing_log_ratio_half hq (by linarith [hx.1]) (hx.2.trans hb)
    exact (mul_pos (by linarith [hx.1]) (by linarith)).ne'
  have hkernel : ContinuousOn (fun x : ℝ => 1 / ((x - 2) * (1 - log x / log q)))
      (Set.Icc a b) :=
    continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_const.sub (hlogc.div_const _))) hden
  have hrho : ContinuousOn (fun x : ℝ => 1 / log x) (Set.Icc a b) :=
    continuousOn_const.div hlogc (fun x hx => (log_pos (by linarith [hx.1])).ne')
  have hui : IntervalIntegrable (fun x => f (log q / log x - 1)) volume a b := by
    apply AntitoneOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hu
  have hv : ContinuousOn (fun x : ℝ => 1 / ((x - 2) * (1 - log x / log q)))
      (uIcc a b) := by simpa only [Set.uIcc_of_le hab] using hkernel
  have hr : ContinuousOn (fun x : ℝ => 1 / log x) (uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hrho
  convert (hui.mul_continuousOn hv).mul_continuousOn hr using 1
  ext x
  simp only [wuPrimeRealWeight]
  ring

/-- True-li increments sampled at the RIGHT endpoint approximate the
actual continuous `p-2` integral. The error is uniform in signed,
possibly discontinuous bounded monotone `f`, and in the right endpoint. -/
theorem primeCoefficient_trueLi_to_continuous
    {f : ℝ → ℝ} {q B : ℝ} (hf : MonotoneOn f (Set.Icc 1 10))
    (hB : 0 ≤ B) (hfb : ∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B)
    {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) (hq : 1 < q) (hlq : 2 ≤ log q)
    (hb : (b : ℝ) ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log (a : ℝ) - 1 ≤ 10) :
    |(∑ n ∈ Finset.Ico a b,
        (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
          wuPrimeCoefficientWeight f q (n + 1)) -
      ∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x| ≤
        12 * B / (a : ℝ) / log a := by
  let u : ℝ → ℝ := fun x => f (log q / log x - 1)
  let v : ℝ → ℝ := fun x => 1 / ((x - 2) * (1 - log x / log q))
  let ρ : ℝ → ℝ := fun x => 1 / log x
  have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hdomain (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) b) :=
    wuPrime_continuous_argument_mem hq (by linarith : 1 < (a : ℝ)) hx hb haq
  have hu : AntitoneOn u (Set.Icc (a : ℝ) b) := by
    intro x hx y hy hxy
    apply hf (hdomain y hy) (hdomain x hx)
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left (log_pos hq).le
        (log_pos (by linarith [hx.1])) (log_le_log (by linarith [hx.1]) hxy)) 1
  have hv : AntitoneOn v (Set.Icc (a : ℝ) b) := by
    intro x hx y hy hxy
    exact (wuPrimeKernel_le hq hlq (haR.trans hx.1) hxy (hy.2.trans hb)).2
  have hv0 (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) b) : 0 ≤ v x :=
    (wuPrimeKernel_le hq hlq (haR.trans hx.1) le_rfl (hx.2.trans hb)).1
  have hlogc : ContinuousOn (fun x : ℝ => log x) (Set.Icc (a : ℝ) b) :=
    continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1])
  have hden (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) b) :
      (x - 2) * (1 - log x / log q) ≠ 0 := by
    have hh := reboxing_log_ratio_half hq (by linarith [hx.1]) (hx.2.trans hb)
    exact (mul_pos (by linarith [hx.1]) (by linarith)).ne'
  have hvc : ContinuousOn v (Set.Icc (a : ℝ) b) :=
    continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_const.sub (hlogc.div_const _))) hden
  have hρc : ContinuousOn ρ (Set.Icc (a : ℝ) b) :=
    continuousOn_const.div hlogc (fun x hx => (log_pos (by linarith [hx.1])).ne')
  have hρ (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) b) :
      0 ≤ ρ x ∧ ρ x ≤ 1 / log (a : ℝ) :=
    ⟨one_div_nonneg.mpr (log_pos (by linarith [hx.1])).le,
      one_div_le_one_div_of_le (log_pos (by linarith))
        (log_le_log (by linarith) hx.1)⟩
  have hquad := antitone_product_right_quadrature hab hu hv hvc hρc hB
    (one_div_nonneg.mpr (log_pos (by linarith : 1 < (a : ℝ))).le)
    (fun x hx => hfb _ (hdomain x hx)) hv0 hρ
  have hli (n : ℕ) (hn : n ∈ Finset.Ico a b) :
      logarithmicIntegral (n + 1) - logarithmicIntegral n =
        ∫ x in (n : ℝ)..(n + 1 : ℕ), ρ x := by
    have hn2 : (2 : ℝ) ≤ n := by
      exact_mod_cast (show 2 ≤ n by have := (mem_Ico.mp hn).1; omega)
    have hni := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable hn2
    have hn1i := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegrand_intervalIntegrable
      (show (2 : ℝ) ≤ (n + 1 : ℕ) by push_cast; linarith)
    simp only [logarithmicIntegral,
      MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral, zero_add]
    convert intervalIntegral.integral_interval_sub_left hn1i hni using 1
    push_cast
    rfl
  have hsum :
      (∑ n ∈ Finset.Ico a b, (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
          wuPrimeCoefficientWeight f q (n + 1)) =
      ∑ n ∈ Finset.Ico a b,
        (∫ x in (n : ℝ)..(n + 1 : ℕ), ρ x) * (u (n + 1) * v (n + 1)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hli n hn]
    simp only [wuPrimeCoefficientWeight, u, v, Nat.cast_add, Nat.cast_one]
    ring
  have hint : (fun x => wuPrimeRealWeight f q x / log x) =
      (fun x => u x * v x * ρ x) := by
    funext x
    simp only [wuPrimeRealWeight, u, v, ρ]
    ring
  rw [hsum, hint]
  apply hquad.trans
  have hva := (reboxing_prime_weight_le_four_div hq haR (habR.trans hb)).2
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hva (show 0 ≤ 3 * B by positivity))
    (show 0 ≤ 1 / log (a : ℝ) by positivity)
  convert h using 1
  ring

end Wu2008DoubleSieve
