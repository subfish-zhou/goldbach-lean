import MathlibNt.Wu2008DoubleSieve.Gamma5GainKernel
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassContinuity

/-!
# Integrability and size of the actual legal Hdelta integral
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gamma5Gain_inner_integrable {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : t ∈ Icc gamma5MassA gamma5ClassicalB) :
    IntervalIntegrable (gamma5GainLiteral δ t) volume t gamma5ClassicalB := by
  apply (gamma5Gain_slice_integrable hδ hδhi t).intervalIntegrable.congr
  intro u hu
  have hu' : u ∈ Icc t gamma5ClassicalB := by
    simpa only [uIcc_of_le ht.2] using uIoc_subset_uIcc hu
  exact gamma5Gain_kernel_eq_literal ht.1 hu'.1 hu'.2

theorem gamma5Gain_inner_eq {δ t : ℝ} (ht : t ∈ Icc gamma5MassA gamma5ClassicalB) :
    (∫ u, gamma5GainKernel δ (t, u)) =
      ∫ u in t..gamma5ClassicalB, gamma5GainLiteral δ t u := by
  have hs : Function.support (fun u => gamma5GainKernel δ (t, u)) ⊆
      Icc t gamma5ClassicalB := by
    intro u hu
    by_cases h : (t, u) ∈ gamma5GainRegion
    · exact ⟨h.1.2.1, h.1.2.2⟩
    · exact False.elim (hu (by simp [gamma5GainKernel, h]))
  rw [truncatedSixthMass_integral_eq_interval ht.2 hs]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc t gamma5ClassicalB := by simpa only [uIcc_of_le ht.2] using hu
  exact gamma5Gain_kernel_eq_literal ht.1 hu'.1 hu'.2

theorem gamma5Gain_outer_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable
      (fun t => ∫ u in t..gamma5ClassicalB, gamma5GainLiteral δ t u)
      volume gamma5MassA gamma5ClassicalB := by
  have h := (gamma5Gain_kernel_integrable hδ hδhi).integral_prod_left
  apply h.intervalIntegrable.congr
  intro t ht
  apply gamma5Gain_inner_eq
  simpa only [uIcc_of_le gamma5Mass_constants.2.1.le] using uIoc_subset_uIcc ht

theorem gamma5Gain_integral_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma5GainIntegral δ = ∫ v : ℝ × ℝ, gamma5GainKernel δ v := by
  have hs : Function.support (fun t => ∫ u, gamma5GainKernel δ (t, u)) ⊆
      Icc gamma5MassA gamma5ClassicalB := by
    intro t ht
    by_contra hn
    apply ht
    change (∫ u, gamma5GainKernel δ (t, u)) = 0
    have he : (fun u => gamma5GainKernel δ (t, u)) = 0 := by
      funext u
      have hh : (t, u) ∉ gamma5GainRegion :=
        fun h => hn (gamma5Gain_triangle_bounds h.1).1
      simp [gamma5GainKernel, hh]
    rw [he]
    simp
  rw [show (∫ v : ℝ × ℝ, gamma5GainKernel δ v) =
      ∫ t, ∫ u, gamma5GainKernel δ (t, u) from
        integral_prod _ (gamma5Gain_kernel_integrable hδ hδhi),
    truncatedSixthMass_integral_eq_interval gamma5Mass_constants.2.1.le hs]
  symm
  apply intervalIntegral.integral_congr
  intro t ht
  exact gamma5Gain_inner_eq (by simpa only [uIcc_of_le gamma5Mass_constants.2.1.le] using ht)

theorem gamma5Gain_literal_bounds {δ t u : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : gamma5MassA ≤ t) (htu : t ≤ u) (hu : u ≤ gamma5ClassicalB) :
    0 ≤ gamma5GainLiteral δ t u ∧ gamma5GainLiteral δ t u ≤ gamma5MassKernel t u := by
  have hb := gamma5Gain_triangle_bounds (v := (t, u)) ⟨ht, htu, hu⟩
  have hh := gamma5Gain_H_bounds hδ hδhi (gamma5GainV t u)
  rw [gamma5GainH, gamma5Gain_clip_eq ⟨hb.2.2.1.le, hb.2.2.2.1.le⟩] at hh
  unfold gamma5GainLiteral gamma5MassKernel
  split_ifs
  · exact ⟨div_nonneg hh.1 hb.2.2.2.2.le,
      div_le_div_of_nonneg_right hh.2 hb.2.2.2.2.le⟩
  · exact ⟨le_rfl, div_nonneg (by norm_num) hb.2.2.2.2.le⟩

theorem gamma5Gain_integral_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    0 ≤ gamma5GainIntegral δ ∧ gamma5GainIntegral δ ≤ gamma5MassC5 := by
  constructor
  · rw [gamma5Gain_integral_eq hδ hδhi]
    exact integral_nonneg (fun v => (gamma5Gain_kernel_bounds hδ hδhi v).1)
  · apply intervalIntegral.integral_mono_on gamma5Mass_constants.2.1.le
      (gamma5Gain_outer_integrable hδ hδhi) gamma5Mass_C5_integrable.2
    intro t ht
    apply intervalIntegral.integral_mono_on ht.2
      (gamma5Gain_inner_integrable hδ hδhi ht) (gamma5Mass_C5_integrable.1 t ht)
    intro u hu
    exact (gamma5Gain_literal_bounds hδ hδhi ht.1 hu.1 hu.2).2

theorem gamma5Gain_H_pullback_ae {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᵐ v : ℝ × ℝ, ContinuousAt (gamma5GainH δ) (gamma5GainV v.1 v.2) := by
  have hmono : Monotone (fun s => -gamma5GainH δ s) := (gamma5Gain_H_antitone hδ hδhi).neg
  have h := truncatedSixthMass_monotone_affine_ae hmono 1 (1 / gamma5ClassicalS)
    (by norm_num [gamma5ClassicalS])
  filter_upwards [h] with v hv
  have he : (1 - v.1 - v.2) / (1 / gamma5ClassicalS) = gamma5GainV v.1 v.2 := by
    simp only [gamma5GainV, div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [he] at hv
  simpa only [Pi.neg_apply, neg_neg, eta] using hv.neg

end Wu2008DoubleSieve
