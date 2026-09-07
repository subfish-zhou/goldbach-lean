import MathlibNt.SieveTheory.LiLiuGoldbachB10ContinuousMain

open MeasureTheory Filter
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Monotonicity of the actual logarithmic integrand gives the sharp left-endpoint denominator. -/
theorem b10_li_difference_le_log_left (κ a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    liuLogarithmicIntegral κ b - liuLogarithmicIntegral κ a ≤ (b - a) / Real.log a := by
  have hi := liuLogarithmicIntegrand_intervalIntegrable_of_two_le ha hab
  have he := intervalIntegral.integral_add_adjacent_intervals
    (liuLogarithmicIntegrand_intervalIntegrable ha) hi
  have hid : liuLogarithmicIntegral κ b - liuLogarithmicIntegral κ a =
      ∫ t in a..b, 1 / Real.log t := by
    unfold liuLogarithmicIntegral
    linarith
  rw [hid]
  have hupper := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (1 : ℝ) / Real.log a))
    (fun t ht => one_div_le_one_div_of_le (Real.log_pos (by linarith : 1 < a))
      (Real.log_le_log (by linarith : 0 < a) ht.1))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, one_mul] using hupper

/-- Scalar relative upper comparison. This is an integral estimate, not a new prime-distribution input. -/
theorem b10_li_interval_relative_upper (ε η : ℝ)
    (hε : 0 < ε) (hεlt : ε < 1) (hη : 0 < η) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ κ : ℝ,
      liuLogarithmicIntegral κ x - liuLogarithmicIntegral κ (ε * x) ≤
        (1 - ε + η) * x / Real.log x := by
  let K : ℝ := -(1 + η) * Real.log ε / η
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop K))
  refine ⟨max 2 (max (2 / ε) x₁), le_max_left _ _, ?_⟩
  intro x hx κ
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith : 1 < x)
  have hxrest : max (2 / ε) x₁ ≤ x := (le_max_right _ _).trans hx
  have hax : 2 ≤ ε * x := by
    have hd : 2 / ε ≤ x := (le_max_left _ _).trans hxrest
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hd
  have hlogax : 0 < Real.log (ε * x) := Real.log_pos (by linarith : 1 < ε * x)
  have hK : K ≤ Real.log x := hx₁ x ((le_max_right _ _).trans hxrest)
  have hpaid : -(1 + η) * Real.log ε ≤ Real.log x * η := (div_le_iff₀ hη).mp hK
  have hratio : Real.log x ≤ (1 + η) * Real.log (ε * x) := by
    rw [Real.log_mul (ne_of_gt hε) (ne_of_gt hxpos)]
    nlinarith
  have hinv : 1 / Real.log (ε * x) ≤ (1 + η) / Real.log x := by
    apply (div_le_div_iff₀ hlogax hlog).mpr
    simpa only [one_mul] using hratio
  have hcoef : (1 - ε) * (1 + η) ≤ 1 - ε + η := by nlinarith
  calc
    _ ≤ (x - ε * x) / Real.log (ε * x) :=
      b10_li_difference_le_log_left κ (ε * x) x hax (by nlinarith)
    _ = ((1 - ε) * x) * (1 / Real.log (ε * x)) := by ring
    _ ≤ ((1 - ε) * x) * ((1 + η) / Real.log x) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = ((1 - ε) * (1 + η)) * x / Real.log x := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hxpos.le) hlog.le

theorem goldbachB10ContinuousMainWeight_relative_upper (ε η : ℝ)
    (hε : 0 < ε) (hεlt : ε < 1) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ,
      0 < m → (m : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) →
      goldbachB10ContinuousMainWeight N ε m ≤
        (1 - ε + η) * ((N : ℝ) / m) / Real.log ((N : ℝ) / m) := by
  obtain ⟨x₀, _hx₀, hx⟩ := b10_li_interval_relative_upper ε η hε hεlt hη
  have hroot := ((tendsto_rpow_atTop (show 0 < (1 : ℝ) / 3 by norm_num)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop x₀)
  obtain ⟨Nr, hr⟩ := eventually_atTop.mp hroot
  refine ⟨max 2 Nr, le_max_left _ _, ?_⟩
  intro N hN m hm hmupper
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlower : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) / m := by
    apply (le_div_iff₀ hmpos).mpr
    calc
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hmupper (Real.rpow_nonneg hNpos.le _)
      _ = N := by rw [← Real.rpow_add hNpos]; norm_num
  simpa only [goldbachB10ContinuousMainWeight, mul_div_assoc] using
    hx ((N : ℝ) / m) ((hr N ((le_max_right _ _).trans hN)).trans hlower) goldbachB10PanKappa0

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig