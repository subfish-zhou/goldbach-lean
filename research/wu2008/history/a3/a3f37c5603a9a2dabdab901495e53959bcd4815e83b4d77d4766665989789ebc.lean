import MathlibNt.Wu2008DoubleSieve.Gamma5GainIntegral
import MathlibNt.Wu2008DoubleSieve.Gamma5GainGeometry

/-!
# Continuous rectangular mass integrals
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma5GainSmooth (v : ℝ × ℝ) : ℝ :=
  1 / (max gamma5MassA v.1 * max gamma5MassA v.2 *
    max (1 - 2 * gamma5ClassicalB) (1 - v.1 - v.2))

theorem gamma5Gain_smooth_den_pos (v : ℝ × ℝ) :
    0 < max gamma5MassA v.1 * max gamma5MassA v.2 *
      max (1 - 2 * gamma5ClassicalB) (1 - v.1 - v.2) := by
  have ha : 0 < gamma5MassA := by norm_num [gamma5MassA, gamma5ClassicalS]
  have hb : 0 < 1 - 2 * gamma5ClassicalB := by norm_num [gamma5ClassicalB]
  exact mul_pos (mul_pos (ha.trans_le (le_max_left _ _)) (ha.trans_le (le_max_left _ _)))
    (hb.trans_le (le_max_left _ _))

theorem gamma5Gain_smooth_continuous : Continuous gamma5GainSmooth := by
  exact continuous_const.div (by fun_prop) (fun v => (gamma5Gain_smooth_den_pos v).ne')

theorem gamma5Gain_smooth_bounds (v : ℝ × ℝ) :
    0 ≤ gamma5GainSmooth v ∧ gamma5GainSmooth v ≤ 400 := by
  have hx : (1 / 10 : ℝ) ≤ max gamma5MassA v.1 := gamma5Mass_constants.1.trans (le_max_left _ _)
  have hy : (1 / 10 : ℝ) ≤ max gamma5MassA v.2 := gamma5Mass_constants.1.trans (le_max_left _ _)
  have hz : (1 / 4 : ℝ) ≤ max (1 - 2 * gamma5ClassicalB) (1 - v.1 - v.2) :=
    (by norm_num [gamma5ClassicalB] : (1 / 4 : ℝ) ≤ 1 - 2 * gamma5ClassicalB).trans (le_max_left _ _)
  have hd := mul_le_mul (mul_le_mul hx hy (by norm_num) (by linarith)) hz (by norm_num)
    (mul_nonneg (by linarith) (by linarith))
  exact ⟨(div_pos (by norm_num) (gamma5Gain_smooth_den_pos v)).le,
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) hd).trans_eq (by norm_num)⟩

theorem gamma5Gain_smooth_eq {t u : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma5ClassicalB)
    (hu : u ∈ Icc gamma5MassA gamma5ClassicalB) :
    gamma5GainSmooth (t, u) = gamma5MassKernel t u := by
  simp only [gamma5GainSmooth, gamma5MassKernel, max_eq_right ht.1, max_eq_right hu.1,
    max_eq_right (show 1 - 2 * gamma5ClassicalB ≤ 1 - t - u by linarith [ht.2, hu.2])]

noncomputable def gamma5GainSmoothRectangle (A B C D : ℝ) : ℝ :=
  ∫ t in A..B, ∫ u in C..D, gamma5GainSmooth (t, u)

theorem gamma5Gain_moving_integral {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {l h : X → ℝ}
    (hf : Continuous f.uncurry) (hl : Continuous l) (hh : Continuous h) :
    Continuous (fun x => ∫ v in l x..h x, f x v) := by
  have hhi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hh
  have hlo := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hl
  convert hhi.sub hlo using 1
  ext x
  exact (intervalIntegral.integral_interval_sub_left
    ((hf.uncurry_left x).intervalIntegrable 0 (h x))
    ((hf.uncurry_left x).intervalIntegrable 0 (l x))).symm

theorem gamma5Gain_smooth_rectangle_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ =>
      gamma5GainSmoothRectangle p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold gamma5GainSmoothRectangle
  apply gamma5Gain_moving_integral
  · apply gamma5Gain_moving_integral
    · exact gamma5Gain_smooth_continuous.comp (by fun_prop)
    · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

theorem gamma5Gain_smooth_rectangle_eq {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hBC : B ≤ C)
    (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    gamma5GainSmoothRectangle A B C D = gamma5MassRectangleIntegral A B C D := by
  unfold gamma5GainSmoothRectangle gamma5MassRectangleIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using ht
  rw [gamma5MassSectionStart, max_eq_left (ht'.2.trans hBC), min_eq_right hCD]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc C D := by simpa only [uIcc_of_le hCD] using hu
  exact gamma5Gain_smooth_eq ⟨hA.trans ht'.1, ht'.2.trans (hBC.trans (hCD.trans hD))⟩
    ⟨hA.trans (hAB.trans (hBC.trans hu'.1)), hu'.2.trans hD⟩

theorem gamma5Gain_rectangle_inner_approx (r : Gamma5GainRectangle) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ r.A + τ < r.B - τ ∧ r.C + τ < r.D - τ ∧
      gamma5MassRectangleIntegral r.A r.B r.C r.D - ε <
        gamma5MassRectangleIntegral (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ) := by
  have ht : Tendsto (fun τ : ℝ =>
      gamma5GainSmoothRectangle (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ))
      (𝓝 0) (𝓝 (gamma5GainSmoothRectangle r.A r.B r.C r.D)) := by
    convert gamma5Gain_smooth_rectangle_continuous.continuousAt.tendsto.comp
      (show Tendsto (fun τ : ℝ => (r.A + τ, r.B - τ, r.C + τ, r.D - τ))
        (𝓝 0) (𝓝 (r.A, r.B, r.C, r.D)) by fun_prop) using 1
  have he := ht.eventually (lt_mem_nhds (sub_lt_self _ hε))
  have hab : ∀ᶠ τ : ℝ in 𝓝 0, r.A + τ < r.B - τ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using r.first)
  have hcd : ∀ᶠ τ : ℝ in 𝓝 0, r.C + τ < r.D - τ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using r.second)
  obtain ⟨τ, hτ, hA, hC, hI⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ).and
    ((hab.and (hcd.and he)).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨τ, hτ, hA, hC, ?_⟩
  rw [gamma5Gain_smooth_rectangle_eq r.lower.le r.first.le r.ordered.le r.second.le r.upper.le,
    gamma5Gain_smooth_rectangle_eq (by linarith [r.lower]) hA.le
      (by linarith [r.ordered]) hC.le (by linarith [r.upper])] at hI
  exact hI

theorem gamma5Gain_smooth_rectangle_indicator {A B C D : ℝ}
    (hAB : A ≤ B) (hCD : C ≤ D) :
    (∫ v : ℝ × ℝ, (Ico A B ×ˢ Ico C D).indicator gamma5GainSmooth v) =
      gamma5GainSmoothRectangle A B C D := by
  have hi : IntegrableOn gamma5GainSmooth (Ico A B ×ˢ Ico C D) :=
    (gamma5Gain_smooth_continuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  rw [integral_indicator (measurableSet_Ico.prod measurableSet_Ico)]
  rw [show (∫ v in Ico A B ×ˢ Ico C D, gamma5GainSmooth v) =
      ∫ t in Ico A B, ∫ u in Ico C D, gamma5GainSmooth (t, u) from setIntegral_prod _ hi]
  simp_rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hCD, ← intervalIntegral.integral_of_le hAB]
  rfl

end Wu2008DoubleSieve
