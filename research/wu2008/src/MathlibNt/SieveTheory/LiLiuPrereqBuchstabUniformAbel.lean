import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabIntegral

/-!
# Uniform prime-sum replacement, including the Buchstab corner

For `primeErrorStart ≤ y`, `y² ≤ x`, and `log x / log y ≤ 100`, the
actual prime sum over `y ≤ p < sqrt x` differs from
`x / log x * ((log x / log y) * buchstab (log x / log y) - 1)` by at most
`106 * (primeErrorEnvelope y + 1 / log y) * (x / log y)`.
For `(y, sqrt x]`, the constant is `104`. Both include `x = y²`.

The proof constructs an integrable derivative representative, splits FTC
at the sole possible interior corner `exp (log x / 3)`, and keeps the
extra `f / log²` integral from the comparator `t / log t`.

The finite summation argument below follows Mathlib's `AbelSummation`
(Xavier Roblot, Apache 2.0), replacing its everywhere differentiability
assumption by the fundamental theorem on subintervals.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace LiLiuPrereqBuchstab

/-- FTC with one exceptional interior point. No derivative at the corner or
at either endpoint is assumed. -/
theorem integral_eq_sub_of_hasDerivAt_off_one {a b c : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ≠ c → HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, g t) = f b - f a := by
  by_cases hca : c ≤ a
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf
      (fun t ht => hd t ht (by linarith [ht.1])) hg
  by_cases hbc : b ≤ c
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf
      (fun t ht => hd t ht (by linarith [ht.2])) hg
  have hac : a ≤ c := (lt_of_not_ge hca).le
  have hcb : c ≤ b := (lt_of_not_ge hbc).le
  have hg' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hg
  have hgac : IntervalIntegrable g volume a c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hac).2
      (hg'.mono_set (Icc_subset_Icc_right hcb))
  have hgcb : IntervalIntegrable g volume c b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcb).2
      (hg'.mono_set (Icc_subset_Icc_left hac))
  have h₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac
    (hf.mono (Icc_subset_Icc_right hcb))
    (fun t ht => hd t ⟨ht.1, ht.2.trans_le hcb⟩ (ne_of_lt ht.2)) hgac
  have h₂ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcb
    (hf.mono (Icc_subset_Icc_left hac))
    (fun t ht => hd t ⟨hac.trans_lt ht.1, ht.2⟩ (ne_of_gt ht.1)) hgcb
  rw [← intervalIntegral.integral_add_adjacent_intervals hgac hgcb, h₁, h₂]
  ring

private theorem sum_indicator_locally (c : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Icc (n : ℝ) (n + 1) →
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = ∑ k ∈ Finset.Icc 0 n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

private theorem integral_mul_sum_of_ftc {a b : ℝ} {f g : ℝ → ℝ}
    (c : ℕ → ℝ)
    (hftc : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (∫ v in s..t, g v) = f t - f s)
    (s t : ℝ) (n : ℕ) (hst : s ≤ t)
    (hn : n ≤ s) (htn : t ≤ n + 1) (has : a ≤ s) (htb : t ≤ b) :
    (∫ v in s..t, g v * ∑ k ∈ Finset.Icc 0 ⌊v⌋₊, c k) =
      (f t - f s) * ∑ k ∈ Finset.Icc 0 n, c k := by
  rw [← hftc s t has hst htb, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [sum_indicator_locally c n] with v hv hv'
  have hmem : v ∈ Icc (n : ℝ) (n + 1) :=
    (Icc_subset_Icc hn htn)
      (Ioc_subset_Icc_self (uIoc_of_le hst ▸ hv'))
  rw [hv hmem]

private theorem cast_between_floors {a b : ℝ} {k : ℕ}
    (hk : k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ b := by
  have h := Finset.mem_Ico.mp hk
  constructor
  · exact ((Nat.floor_lt' (by omega : k ≠ 0)).mp h.1).le
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact h.2

/-- Abel summation for an integrable derivative representative with FTC on
every subinterval. This also applies to continuous piecewise-C¹ weights. -/
theorem sum_mul_abel_of_ftc {a b : ℝ} {f g : ℝ → ℝ}
    (c : ℕ → ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b))
    (hftc : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (∫ v in s..t, g v) = f t - f s) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) -
      f a * (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, c k) -
        ∫ t in a..b, g t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  have aux1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have aux2 : b ≤ (⌊b⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Finset.Ioc_eq_empty_of_le le_rfl, Finset.sum_empty, ← sub_mul,
      integral_mul_sum_of_ftc c hftc _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl,
      sub_self]
  have aux3 : a ≤ (⌊a⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : (⌊a⌋₊ : ℝ) + 1 ≤ b := by
    rwa [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (ha.trans hab)
  have aux6 : a ≤ (⌊b⌋₊ : ℝ) := (Nat.floor_lt ha |>.mp hb).le
  simp_rw [← smul_eq_mul, Finset.sum_Ioc_by_parts (fun k => f k) _ hb,
    Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc, smul_eq_mul]
  have hsum :
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ (⌊b⌋₊ - 1),
        (f ↑(k + 1) - f k) * ∑ n ∈ Finset.Icc 0 k, c n =
      ∑ k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊,
        ∫ t in (k : ℝ)..↑(k + 1), g t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (by omega), Eq.comm]
    exact Finset.sum_congr rfl fun k hk =>
      integral_mul_sum_of_ftc c hftc _ _ _ (mod_cast k.le_succ)
        le_rfl (mod_cast le_rfl) (cast_between_floors hk).1
        (mod_cast (cast_between_floors hk).2)
  rw [hsum, intervalIntegral.sum_integral_adjacent_intervals_Ico hb,
    Nat.cast_add, Nat.cast_one,
    ← intervalIntegral.integral_interval_sub_left (a := a) (c := (⌊a⌋₊ : ℝ) + 1),
    ← intervalIntegral.integral_add_adjacent_intervals (b := (⌊b⌋₊ : ℝ)) (c := b),
    integral_mul_sum_of_ftc c hftc _ _ _ aux3 aux1 le_rfl le_rfl aux4,
    integral_mul_sum_of_ftc c hftc _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le aux6).2
      ((integrableOn_mul_sum_Icc c ha hg).mono_set (Icc_subset_Icc_right aux5))
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le aux5).2
      ((integrableOn_mul_sum_Icc c ha hg).mono_set (Icc_subset_Icc_left aux6))
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le aux6).2
      ((integrableOn_mul_sum_Icc c ha hg).mono_set (Icc_subset_Icc_right aux5))
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le aux3).2
      ((integrableOn_mul_sum_Icc c ha hg).mono_set (Icc_subset_Icc_right aux4))
  · intro k hk
    have hk' : k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊ := Finset.mem_Ico.mpr hk
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast k.le_succ)).2
      ((integrableOn_mul_sum_Icc c ha hg).mono_set
        (Icc_subset_Icc (cast_between_floors hk').1
          (by exact_mod_cast (cast_between_floors hk').2)))

/-- Actual prime Abel summation with a single corner. The derivative
representative need not equal `deriv f` at the corner or the endpoints. -/
theorem prime_abel_off_one {a b c : ℝ} {f g : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ≠ c → HasDerivAt f (g t) t)
    (hg : IntegrableOn g (Icc a b)) :
    ∑ p ∈ primesIoc a b, f p =
      f b * primePi b - f a * primePi a -
        ∫ t in a..b, g t * primePi t := by
  have hftc : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (∫ v in s..t, g v) = f t - f s := by
    intro s t has hst htb
    exact integral_eq_sub_of_hasDerivAt_off_one hst
      (hf.mono (Icc_subset_Icc has htb))
      (fun v hv hvc => hd v ⟨has.trans_lt hv.1, hv.2.trans_le htb⟩ hvc)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).2
        (hg.mono_set (Icc_subset_Icc has htb)))
  have h := sum_mul_abel_of_ftc
    (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) ha hab hg hftc
  simp only [← primePi_eq_sum_indicator] at h
  have hs : primesIoc a b = (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext p
    simp only [primesIoc, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ioc,
      Nat.floor_lt ha]
    tauto
  rw [hs, Finset.sum_filter]
  simpa only [mul_ite, mul_one, mul_zero] using h

/-- A derivative representative; the chosen value at `2` is immaterial. -/
noncomputable def buchstabSlope (u : ℝ) : ℝ :=
  if u ≤ 2 then -(1 / u ^ 2) else (buchstab (u - 1) - buchstab u) / u

theorem measurable_buchstabSlope : Measurable buchstabSlope := by
  unfold buchstabSlope
  exact Measurable.ite measurableSet_Iic
    ((measurable_const.div (measurable_id.pow_const 2)).neg)
    (((continuous_buchstab.measurable.comp (measurable_id.sub measurable_const)).sub
      continuous_buchstab.measurable).div measurable_id)

theorem hasDerivAt_buchstab_off_two {u : ℝ} (hu : 1 < u) (hu2 : u ≠ 2) :
    HasDerivAt buchstab (buchstabSlope u) u := by
  by_cases h : u ≤ 2
  · have hlt : u < 2 := lt_of_le_of_ne h hu2
    have hd := (hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_id u) (by linarith : u ≠ 0)
    have hd' : HasDerivAt (fun v : ℝ => 1 / v) (buchstabSlope u) u := by
      convert! hd using 1
      simp [buchstabSlope, h, neg_div]
    apply hd'.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hlt] with v hv hv2
    exact buchstab_eq_one_div hv.le hv2.le
  · simpa [buchstabSlope, h] using hasDerivAt_buchstab (lt_of_not_ge h)

theorem abs_buchstabSlope_le_one {u : ℝ} (hu : 1 ≤ u) :
    |buchstabSlope u| ≤ 1 := by
  by_cases h : u ≤ 2
  · rw [buchstabSlope, if_pos h, abs_neg, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity : 0 < u ^ 2)).2 (by nlinarith)
  · have hu2 : 2 < u := lt_of_not_ge h
    rw [buchstabSlope, if_neg h, ← deriv_buchstab hu2]
    exact (abs_deriv_buchstab_le hu2).trans
      ((div_le_one (by positivity : 0 < 2 * u)).2 (by linarith))

/-- The actual weight occurring in the rough-count recursion. -/
noncomputable def buchstabPrimeKernel (x t : ℝ) : ℝ :=
  x / (t * Real.log t) * buchstab (Real.log x / Real.log t - 1)

/-- Factored derivative representative, including an arbitrary corner value. -/
noncomputable def buchstabPrimeKernelSlope (x t : ℝ) : ℝ :=
  -(x / (t ^ 2 * Real.log t)) *
    ((1 + 1 / Real.log t) * buchstab (Real.log x / Real.log t - 1) +
      (Real.log x / Real.log t) / Real.log t *
        buchstabSlope (Real.log x / Real.log t - 1))

theorem measurable_buchstabPrimeKernelSlope (x : ℝ) :
    Measurable (buchstabPrimeKernelSlope x) := by
  unfold buchstabPrimeKernelSlope
  have hw := continuous_buchstab.measurable
  have hs := measurable_buchstabSlope
  fun_prop

theorem continuousOn_buchstabPrimeKernel {a b : ℝ} (x : ℝ) (ha : 1 < a) :
    ContinuousOn (buchstabPrimeKernel x) (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  unfold buchstabPrimeKernel
  apply ContinuousAt.continuousWithinAt
  have hw := continuous_buchstab
  fun_prop (disch := simp_all)

theorem hasDerivAt_buchstabPrimeKernel {x t : ℝ}
    (ht : 1 < t) (hu : 1 < Real.log x / Real.log t - 1)
    (hu2 : Real.log x / Real.log t - 1 ≠ 2) :
    HasDerivAt (buchstabPrimeKernel x) (buchstabPrimeKernelSlope x t) t := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hweight := (hasDerivAt_const t x).div
    ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)) (mul_ne_zero ht0 hl0)
  have harg := ((hasDerivAt_const t (Real.log x)).div
    (Real.hasDerivAt_log ht0) hl0).sub_const 1
  convert! hweight.mul ((hasDerivAt_buchstab_off_two hu hu2).comp t harg) using 1
  dsimp [buchstabPrimeKernelSlope]
  field_simp
  ring

private theorem kernel_range {x y t : ℝ} (hy : primeErrorStart ≤ y)
    (hxy : y ^ 2 ≤ x) (ht : t ∈ Icc y (Real.sqrt x)) :
    0 ≤ x ∧ 1 ≤ Real.log t ∧ 2 ≤ Real.log x / Real.log t := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have ht1 := hy1.trans_le ht.1
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  refine ⟨hx0, one_le_log_of_start_le (hy.trans ht.1), ?_⟩
  apply (le_div_iff₀ (Real.log_pos ht1)).2
  have hs : t ^ 2 ≤ x := (Real.le_sqrt (by linarith) hx0).1 ht.2
  have hl := Real.log_le_log (sq_pos_of_pos (by linarith : 0 < t)) hs
  simpa only [Real.log_pow, Nat.cast_ofNat] using hl

theorem abs_buchstabPrimeKernel_le {x t : ℝ} (hx : 0 ≤ x)
    (ht : 1 < t) (hu : 1 ≤ Real.log x / Real.log t - 1) :
    |buchstabPrimeKernel x t| ≤ x / (t * Real.log t) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl0 := Real.log_pos ht
  rw [buchstabPrimeKernel, abs_mul, abs_of_nonneg (by positivity),
    abs_of_nonneg (buchstab_nonneg hu)]
  exact mul_le_of_le_one_right (by positivity) (buchstab_le_one hu)

/-- Uniform differential bound on the entire compact parameter band. -/
theorem abs_buchstabPrimeKernelSlope_le {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 < t) (hl : 1 ≤ Real.log t)
    (hu : 1 ≤ Real.log x / Real.log t - 1)
    (hU : Real.log x / Real.log t ≤ 100) :
    |buchstabPrimeKernelSlope x t| ≤ 102 * (x / (t ^ 2 * Real.log t)) := by
  have hl0 : 0 < Real.log t := by linarith
  have hi : 0 ≤ 1 / Real.log t := by positivity
  have hi1 : 1 / Real.log t ≤ 1 := (div_le_one hl0).2 hl
  have hv : 0 ≤ Real.log x / Real.log t := by linarith
  have hv' : 0 ≤ (Real.log x / Real.log t) / Real.log t := by positivity
  have hv100 : (Real.log x / Real.log t) / Real.log t ≤ 100 := by
    calc
      _ = (Real.log x / Real.log t) * (1 / Real.log t) := by ring
      _ ≤ (Real.log x / Real.log t) * 1 := mul_le_mul_of_nonneg_left hi1 hv
      _ ≤ 100 := by simpa using hU
  have hw : |(1 + 1 / Real.log t) * buchstab (Real.log x / Real.log t - 1)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (buchstab_nonneg hu)]
    have hm := mul_le_of_le_one_right (by positivity : 0 ≤ 1 + 1 / Real.log t)
      (buchstab_le_one hu)
    linarith
  have hs : |(Real.log x / Real.log t) / Real.log t *
      buchstabSlope (Real.log x / Real.log t - 1)| ≤ 100 := by
    rw [abs_mul, abs_of_nonneg hv']
    exact (mul_le_of_le_one_right hv' (abs_buchstabSlope_le_one hu)).trans hv100
  rw [buchstabPrimeKernelSlope, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  have hb := (abs_add_le
    ((1 + 1 / Real.log t) * buchstab (Real.log x / Real.log t - 1))
    ((Real.log x / Real.log t) / Real.log t *
      buchstabSlope (Real.log x / Real.log t - 1))).trans (add_le_add hw hs)
  calc
    _ ≤ (x / (t ^ 2 * Real.log t)) * (2 + 100) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private theorem kernel_parameter_le {x y t : ℝ} (hy : primeErrorStart ≤ y)
    (hxy : y ^ 2 ≤ x) (hU : Real.log x / Real.log y ≤ 100) (hyt : y ≤ t) :
    Real.log x / Real.log t ≤ 100 := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx1 : 1 < x := by nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < y) hyt
  exact (div_le_div_of_nonneg_left (Real.log_pos hx1).le (Real.log_pos hy1) hlog).trans hU

theorem integrableOn_buchstabPrimeKernelSlope {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x)
    (hU : Real.log x / Real.log y ≤ 100) :
    IntegrableOn (buchstabPrimeKernelSlope x) (Icc y (Real.sqrt x)) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hc : ContinuousOn (fun t : ℝ => 102 * (x / (t ^ 2 * Real.log t)))
      (Icc y (Real.sqrt x)) := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans (hy1.trans_le ht.1)).ne'
    have hl0 : Real.log t ≠ 0 := (Real.log_pos (hy1.trans_le ht.1)).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := simp_all)
  apply hc.integrableOn_Icc.mono' (measurable_buchstabPrimeKernelSlope x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  have hr := kernel_range hy hxy ht
  exact abs_buchstabPrimeKernelSlope_le hr.1 (by linarith [ht.1]) hr.2.1
    (by linarith [hr.2.2]) (kernel_parameter_le hy hxy hU ht.1)

private theorem kernel_hasDerivAt_on_band {x y t : ℝ}
    (hy : primeErrorStart ≤ y)
    (ht : t ∈ Ioo y (Real.sqrt x)) (htc : t ≠ Real.exp (Real.log x / 3)) :
    HasDerivAt (buchstabPrimeKernel x) (buchstabPrimeKernelSlope x t) t := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have ht1 : 1 < t := hy1.trans ht.1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hl0 := Real.log_pos ht1
  have hu : 1 < Real.log x / Real.log t - 1 := by
    have hs : t ^ 2 < x := (Real.lt_sqrt ht0.le).1 ht.2
    have hl := Real.log_lt_log (sq_pos_of_pos ht0) hs
    rw [Real.log_pow] at hl
    have : 2 < Real.log x / Real.log t := (lt_div_iff₀ hl0).2 (by simpa using hl)
    linarith
  apply hasDerivAt_buchstabPrimeKernel ht1 hu
  intro heq
  have hdiv : Real.log x / Real.log t = 3 := by linarith
  have hlog : Real.log t = Real.log x / 3 := by
    have := (div_eq_iff hl0.ne').1 hdiv
    linarith
  exact htc ((Real.exp_log ht0).symm.trans (congrArg Real.exp hlog))

/-- The actual prime kernel satisfies Abel summation, even when
`exp (log x / 3)` lies in the interval. -/
theorem buchstabPrimeKernel_abel {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x)
    (hU : Real.log x / Real.log y ≤ 100) :
    ∑ p ∈ primesIoc y (Real.sqrt x), buchstabPrimeKernel x p =
      buchstabPrimeKernel x (Real.sqrt x) * primePi (Real.sqrt x) -
      buchstabPrimeKernel x y * primePi y -
      ∫ t in y..Real.sqrt x, buchstabPrimeKernelSlope x t * primePi t := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  exact prime_abel_off_one (c := Real.exp (Real.log x / 3))
    (by linarith) (Real.le_sqrt_of_sq_le hxy)
    (continuousOn_buchstabPrimeKernel x hy1)
    (fun _ ht htc => kernel_hasDerivAt_on_band hy ht htc)
    (integrableOn_buchstabPrimeKernelSlope hy hxy hU)

private theorem continuousOn_log_quotient {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => t / Real.log t) (Icc a b) := by
  intro t ht
  have ht1 := ha.trans_le ht.1
  exact (continuousAt_id.div (Real.continuousAt_log (by linarith : t ≠ 0))
    (Real.log_pos ht1).ne').continuousWithinAt

private theorem hasDerivAt_log_quotient {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => s / Real.log s)
      (1 / Real.log t - 1 / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 := (Real.log_pos ht).ne'
  convert! (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl0 using 1
  dsimp
  field_simp

/-- Subtracting `t / log t`, not `Li(t)`, leaves an explicit extra
`f(t) / log² t` integral. -/
theorem prime_abel_log_error_identity {a b c : ℝ} {f g : ℝ → ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ≠ c → HasDerivAt f (g t) t)
    (hg : IntegrableOn g (Icc a b)) :
    (∑ p ∈ primesIoc a b, f p) - (∫ t in a..b, f t / Real.log t) =
      f b * (primePi b - b / Real.log b) -
      f a * (primePi a - a / Real.log a) -
      (∫ t in a..b, g t * (primePi t - t / Real.log t)) -
      (∫ t in a..b, f t / Real.log t ^ 2) := by
  have hm := continuousOn_log_quotient (b := b) ha
  have hl : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Icc a b) := by
    intro t ht
    have ht1 := ha.trans_le ht.1
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith : t ≠ 0))
      (Real.log_pos ht1).ne').continuousWithinAt
  have hl2 : ContinuousOn (fun t : ℝ => 1 / Real.log t ^ 2) (Icc a b) := by
    simpa only [Pi.pow_def, one_div_pow] using hl.pow 2
  have hgM : IntervalIntegrable (fun t => g t * (t / Real.log t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (hg.mul_continuousOn hm isCompact_Icc)
  have hfL : IntervalIntegrable (fun t => f t / Real.log t) volume a b := by
    simpa only [Pi.mul_def, div_eq_mul_inv, one_div, one_mul] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab (μ := volume)).2
        (hf.mul hl).integrableOn_Icc
  have hfL2 : IntervalIntegrable (fun t => f t / Real.log t ^ 2) volume a b := by
    simpa only [Pi.mul_def, div_eq_mul_inv, one_div, one_mul] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab (μ := volume)).2
        (hf.mul hl2).integrableOn_Icc
  have hFTC := integral_eq_sub_of_hasDerivAt_off_one (c := c) hab (hf.mul hm)
    (g := fun t => g t * (t / Real.log t) + (f t / Real.log t - f t / Real.log t ^ 2))
    (fun t ht htc => by
      convert! (hd t ht htc).mul (hasDerivAt_log_quotient (ha.trans ht.1)) using 1
      ring)
    (hgM.add (hfL.sub hfL2))
  rw [intervalIntegral.integral_add hgM (hfL.sub hfL2),
    intervalIntegral.integral_sub hfL hfL2] at hFTC
  have hgPi : IntervalIntegrable (fun t => g t * primePi t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (integrableOn_mul_primePi (by linarith) hg)
  have hsplit :
      (∫ t in a..b, g t * (primePi t - t / Real.log t)) =
      (∫ t in a..b, g t * primePi t) - (∫ t in a..b, g t * (t / Real.log t)) := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hgPi hgM
  rw [prime_abel_off_one (by linarith) hab hf hd hg, hsplit]
  simp only [Pi.mul_apply] at hFTC
  nlinarith [hFTC]

private theorem continuousOn_inv_mul_log_sq {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := (zero_lt_one.trans (ha.trans_le ht.1)).ne'
  have hl0 : Real.log t ≠ 0 := (Real.log_pos (ha.trans_le ht.1)).ne'
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp_all)

theorem integral_inv_mul_log_sq_le {a b : ℝ}
    (ha : primeErrorStart ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t ^ 2)) ≤ 1 / Real.log a := by
  have h := integral_logTailKernel ha hab
  have he : (∫ t in a..b, 4 / (t * Real.log t ^ 2)) =
      4 * (∫ t in a..b, 1 / (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [he] at h
  have hlb : 0 < Real.log b := by
    linarith [one_le_log_of_start_le (ha.trans hab)]
  have hn : 0 ≤ 4 / Real.log b := by positivity
  linarith [show 4 / Real.log a = 4 * (1 / Real.log a) by ring]

private theorem abs_integral_le_log_tail {a b K : ℝ} {g : ℝ → ℝ}
    (ha : primeErrorStart ≤ a) (hab : a ≤ b) (hK : 0 ≤ K)
    (hg : IntervalIntegrable g volume a b)
    (hb : ∀ t ∈ Icc a b, |g t| ≤ K * (1 / (t * Real.log t ^ 2))) :
    |∫ t in a..b, g t| ≤ K / Real.log a := by
  have ha1 : 1 < a := by linarith [primeErrorStart_spec.1]
  have hi : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (continuousOn_inv_mul_log_sq ha1).integrableOn_Icc
  calc
    _ ≤ ∫ t in a..b, |g t| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, K * (1 / (t * Real.log t ^ 2)) :=
      intervalIntegral.integral_mono_on hab hg.abs (hi.const_mul K) hb
    _ = K * (∫ t in a..b, 1 / (t * Real.log t ^ 2)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ K * (1 / Real.log a) :=
      mul_le_mul_of_nonneg_left (integral_inv_mul_log_sq_le ha hab) hK
    _ = _ := by ring

private theorem prime_error_endpoint_le {a t X : ℝ} {f : ℝ → ℝ}
    (ha : primeErrorStart ≤ a) (hat : a ≤ t) (hX : 0 ≤ X)
    (hf : |f t| ≤ X / (t * Real.log t)) :
    |f t * (primePi t - t / Real.log t)| ≤
      primeErrorEnvelope a * (X / Real.log a) := by
  have ha1 : 1 < a := by linarith [primeErrorStart_spec.1]
  have ht0 : 0 < t := zero_lt_one.trans (ha1.trans_le hat)
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hlt : 0 < Real.log t := Real.log_pos (ha1.trans_le hat)
  have hl1 := one_le_log_of_start_le (ha.trans hat)
  have hlam := Real.log_le_log (zero_lt_one.trans ha1) hat
  have hlogs : Real.log a ≤ Real.log t ^ 2 := by nlinarith
  calc
    _ = |f t| * |primePi t - t / Real.log t| := abs_mul _ _
    _ ≤ (X / (t * Real.log t)) * (primeErrorEnvelope a * (t / Real.log t)) :=
      mul_le_mul hf (primePi_error_le ha hat) (abs_nonneg _) (by positivity)
    _ = (primeErrorEnvelope a * X) / Real.log t ^ 2 := by field_simp
    _ ≤ (primeErrorEnvelope a * X) / Real.log a :=
      div_le_div_of_nonneg_left
        (mul_nonneg (primeErrorEnvelope_nonneg a) hX) hla hlogs
    _ = _ := by ring

/-- A quantitative, parameter-independent Abel estimate from the actual PNT.
The only weight assumptions are continuity, an integrable piecewise
derivative, and explicit pointwise bounds. -/
theorem prime_abel_log_error_le {a b c X A : ℝ} {f g : ℝ → ℝ}
    (ha : primeErrorStart ≤ a) (hab : a ≤ b) (hX : 0 ≤ X) (hA : 0 ≤ A)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ≠ c → HasDerivAt f (g t) t)
    (hg : IntegrableOn g (Icc a b))
    (hfBound : ∀ t ∈ Icc a b, |f t| ≤ X / (t * Real.log t))
    (hgBound : ∀ t ∈ Icc a b, |g t| ≤ A * (X / (t ^ 2 * Real.log t))) :
    |(∑ p ∈ primesIoc a b, f p) - (∫ t in a..b, f t / Real.log t)| ≤
      (A + 2) * primeErrorEnvelope a * (X / Real.log a) + X / Real.log a ^ 2 := by
  have ha1 : 1 < a := by linarith [primeErrorStart_spec.1]
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hδ := primeErrorEnvelope_nonneg a
  have hgM := hg.mul_continuousOn (continuousOn_log_quotient ha1) isCompact_Icc
  have hgE : IntervalIntegrable (fun t => g t * (primePi t - t / Real.log t)) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    simpa only [Pi.sub_def, mul_sub] using
      (integrableOn_mul_primePi (by linarith) hg).sub hgM
  have hE : |∫ t in a..b, g t * (primePi t - t / Real.log t)| ≤
      (A * primeErrorEnvelope a * X) / Real.log a := by
    apply abs_integral_le_log_tail ha hab (by positivity) hgE
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans (ha1.trans_le ht.1)
    have hlt := Real.log_pos (ha1.trans_le ht.1)
    calc
      _ = |g t| * |primePi t - t / Real.log t| := abs_mul _ _
      _ ≤ (A * (X / (t ^ 2 * Real.log t))) *
          (primeErrorEnvelope a * (t / Real.log t)) :=
        mul_le_mul (hgBound t ht) (primePi_error_le ha ht.1)
          (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hfL2c : ContinuousOn (fun t => f t / Real.log t ^ 2) (Icc a b) := by
    apply hf.div
    · exact (Real.continuousOn_log.mono (fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith [ht.1])).pow 2
    · intro t ht
      exact pow_ne_zero 2 (Real.log_pos (ha1.trans_le ht.1)).ne'
  have hL2 : |∫ t in a..b, f t / Real.log t ^ 2| ≤
      (X / Real.log a) / Real.log a := by
    apply abs_integral_le_log_tail ha hab (by positivity)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hfL2c.integrableOn_Icc)
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans (ha1.trans_le ht.1)
    have hlt := Real.log_pos (ha1.trans_le ht.1)
    calc
      _ = |f t| / Real.log t ^ 2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg (Real.log t))]
      _ ≤ (X / (t * Real.log t)) / Real.log t ^ 2 :=
        div_le_div_of_nonneg_right (hfBound t ht) (sq_nonneg _)
      _ = (X / Real.log t) * (1 / (t * Real.log t ^ 2)) := by ring
      _ ≤ (X / Real.log a) * (1 / (t * Real.log t ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hX hla
            (Real.log_le_log (zero_lt_one.trans ha1) ht.1)) (by positivity)
  have hea := prime_error_endpoint_le ha le_rfl hX (hfBound a ⟨le_rfl, hab⟩)
  have heb := prime_error_endpoint_le ha hab hX (hfBound b ⟨hab, le_rfl⟩)
  rw [prime_abel_log_error_identity ha1 hab hf hd hg]
  apply abs_le.mpr
  constructor <;>
    nlinarith [(abs_le.mp hea).1, (abs_le.mp hea).2,
      (abs_le.mp heb).1, (abs_le.mp heb).2,
      (abs_le.mp hE).1, (abs_le.mp hE).2,
      (abs_le.mp hL2).1, (abs_le.mp hL2).2,
      show (A * primeErrorEnvelope a * X) / Real.log a =
        A * primeErrorEnvelope a * (X / Real.log a) by ring,
      show X / Real.log a / Real.log a = X / Real.log a ^ 2 by ring]

/-- Uniform prime-sum replacement on `(y, sqrt x]`, with a numerical constant
independent of both real parameters, including `x = y²`. -/
theorem buchstabPrimeKernel_sum_Ioc_error_le {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x)
    (hU : Real.log x / Real.log y ≤ 100) :
    |(∑ p ∈ primesIoc y (Real.sqrt x), buchstabPrimeKernel x p) -
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
      104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  have h := prime_abel_log_error_le (c := Real.exp (Real.log x / 3))
    (X := x) (A := 102) hy (Real.le_sqrt_of_sq_le hxy) hx0 (by norm_num)
    (continuousOn_buchstabPrimeKernel x hy1)
    (fun _ ht htc => kernel_hasDerivAt_on_band hy ht htc)
    (integrableOn_buchstabPrimeKernelSlope hy hxy hU)
    (fun t ht => by
      have hr := kernel_range hy hxy ht
      exact abs_buchstabPrimeKernel_le hr.1 (hy1.trans_le ht.1) (by linarith [hr.2.2]))
    (fun t ht => by
      have hr := kernel_range hy hxy ht
      exact abs_buchstabPrimeKernelSlope_le hr.1 (by linarith [ht.1]) hr.2.1
        (by linarith [hr.2.2]) (kernel_parameter_le hy hxy hU ht.1))
  have he :
      (∫ t in y..Real.sqrt x, buchstabPrimeKernel x t / Real.log t) =
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1) := by
    rw [← mul_integral_buchstab_log_kernel_sqrt hy1 hxy,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [buchstabPrimeKernel]
    ring
  rw [he] at h
  calc
    _ ≤ (102 + 2) * primeErrorEnvelope y * (x / Real.log y) + x / Real.log y ^ 2 := h
    _ ≤ 104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
      have hp : 0 ≤ x / Real.log y ^ 2 := by positivity
      have heq : 104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) =
          104 * primeErrorEnvelope y * (x / Real.log y) + 104 * (x / Real.log y ^ 2) := by ring
      rw [heq]
      nlinarith

/-- The lower prime cutoff is included, the upper cutoff is excluded. -/
noncomputable def primesIco (a b : ℝ) : Finset ℕ :=
  (primesIcc a b).filter (fun p => (p : ℝ) < b)

theorem mem_primesIco {a b : ℝ} (hb : 0 ≤ b) {p : ℕ} :
    p ∈ primesIco a b ↔ p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b := by
  simp only [primesIco, Finset.mem_filter, mem_primesIcc hb]
  constructor
  · rintro ⟨⟨hp, ha, _⟩, hpb⟩
    exact ⟨hp, ha, hpb⟩
  · rintro ⟨hp, ha, hpb⟩
    exact ⟨⟨hp, ha, hpb.le⟩, hpb⟩

/-- Exact upper-endpoint correction, also valid on a degenerate interval. -/
theorem sum_primesIcc_eq_sum_primesIco_add {a b : ℝ} (hb : 0 ≤ b) (f : ℝ → ℝ) :
    ∑ p ∈ primesIcc a b, f p =
      (∑ p ∈ primesIco a b, f p) +
        if ∃ p ∈ primesIcc a b, (p : ℝ) = b then f b else 0 := by
  classical
  by_cases he : ∃ p ∈ primesIcc a b, (p : ℝ) = b
  · obtain ⟨p, hp, hpb⟩ := he
    have hs : primesIcc a b = insert p (primesIco a b) := by
      ext q
      rw [mem_primesIcc hb, Finset.mem_insert, mem_primesIco hb]
      constructor
      · intro hq
        by_cases hqp : q = p
        · exact Or.inl hqp
        · refine Or.inr ⟨hq.1, hq.2.1, lt_of_le_of_ne hq.2.2 ?_⟩
          intro hqb
          exact hqp (Nat.cast_injective (hqb.trans hpb.symm))
      · rintro (rfl | hq)
        · exact (mem_primesIcc hb).1 hp
        · exact ⟨hq.1, hq.2.1, hq.2.2.le⟩
    have hn : p ∉ primesIco a b := by
      intro h
      have hlt := ((mem_primesIco hb).1 h).2.2
      simp [hpb] at hlt
    rw [if_pos ⟨p, hp, hpb⟩, hs, Finset.sum_insert hn, hpb, add_comm]
  · have hs : primesIcc a b = primesIco a b := by
      ext p
      rw [mem_primesIcc hb, mem_primesIco hb]
      constructor
      · intro hp
        refine ⟨hp.1, hp.2.1, lt_of_le_of_ne hp.2.2 ?_⟩
        intro hpb
        exact he ⟨p, (mem_primesIcc hb).2 hp, hpb⟩
      · intro hp
        exact ⟨hp.1, hp.2.1, hp.2.2.le⟩
    rw [if_neg he, hs, add_zero]

private theorem kernel_endpoint_le {x y t : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) (ht : t ∈ Icc y (Real.sqrt x)) :
    |buchstabPrimeKernel x t| ≤ x / Real.log y ^ 2 := by
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have ht0 : 0 < t := hy0.trans_le ht.1
  have hly := Real.log_pos hy1
  have hlt := Real.log_pos (hy1.trans_le ht.1)
  have hr := kernel_range hy hxy ht
  have hlyt : Real.log y ≤ t :=
    (le_trans (Real.log_le_sub_one_of_pos hy0) (by linarith)).trans ht.1
  have hden : Real.log y ^ 2 ≤ t * Real.log t := by
    rw [pow_two]
    exact mul_le_mul hlyt (Real.log_le_log hy0 ht.1) hly.le ht0.le
  exact (abs_buchstabPrimeKernel_le hr.1 (hy1.trans_le ht.1) (by linarith [hr.2.2])).trans
    (div_le_div_of_nonneg_left hr.1 (sq_pos_of_pos hly) hden)

/-- Uniform replacement (H) with the actual strict-upper prime cutoff
`y ≤ p < sqrt x`. The explicit constant `106` works for every admissible
`x,y`; no differentiability is asserted at the Buchstab corner. -/
theorem buchstabPrimeKernel_sum_Ico_error_le {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x)
    (hU : Real.log x / Real.log y ≤ 100) :
    |(∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
      106 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
  classical
  have hyb : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxy
  have hlow := sum_primesIcc_eq_sum_primesIoc_add (Real.sqrt_nonneg x) (buchstabPrimeKernel x)
    (y := y)
  have hupp := sum_primesIcc_eq_sum_primesIco_add (Real.sqrt_nonneg x) (buchstabPrimeKernel x)
    (a := y)
  have hL :
      |if ∃ p ∈ primesIcc y (Real.sqrt x), (p : ℝ) = y then buchstabPrimeKernel x y else 0| ≤
        x / Real.log y ^ 2 := by
    split_ifs
    · exact kernel_endpoint_le hy hxy ⟨le_rfl, hyb⟩
    · have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
      simp only [abs_zero]
      positivity
  have hB :
      |if ∃ p ∈ primesIcc y (Real.sqrt x), (p : ℝ) = Real.sqrt x then
        buchstabPrimeKernel x (Real.sqrt x) else 0| ≤ x / Real.log y ^ 2 := by
    split_ifs
    · exact kernel_endpoint_le hy hxy ⟨hyb, le_rfl⟩
    · have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
      simp only [abs_zero]
      positivity
  have hH := buchstabPrimeKernel_sum_Ioc_error_le hy hxy hU
  have hsum :
      |(∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
        x / Real.log x *
          ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
      104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) +
        2 * (x / Real.log y ^ 2) := by
    apply abs_le.mpr
    constructor <;>
      linarith [(abs_le.mp hL).1, (abs_le.mp hL).2,
        (abs_le.mp hB).1, (abs_le.mp hB).2,
        (abs_le.mp hH).1, (abs_le.mp hH).2]
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  have hly := Real.log_pos hy1
  have hδ := primeErrorEnvelope_nonneg y
  have hnonneg : 0 ≤ primeErrorEnvelope y * (x / Real.log y) := by positivity
  refine hsum.trans ?_
  have he :
      106 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) =
      104 * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) +
        2 * (x / Real.log y ^ 2) + 2 * (primeErrorEnvelope y * (x / Real.log y)) := by ring
  rw [he]
  linarith

/-- The constant is quantified before both parameters. The summand and main
term are the actual Buchstab kernel, not abstract replacement interfaces. -/
theorem buchstab_prime_sum_replacement_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ,
      primeErrorStart ≤ y → y ^ 2 ≤ x → Real.log x / Real.log y ≤ 100 →
      |(∑ p ∈ primesIco y (Real.sqrt x),
        x / ((p : ℝ) * Real.log p) * buchstab (Real.log x / Real.log p - 1)) -
        x / Real.log x *
          ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| ≤
        C * (primeErrorEnvelope y + 1 / Real.log y) * (x / Real.log y) := by
  refine ⟨106, by norm_num, ?_⟩
  intro x y hy hxy hU
  exact buchstabPrimeKernel_sum_Ico_error_le hy hxy hU

end LiLiuPrereqBuchstab