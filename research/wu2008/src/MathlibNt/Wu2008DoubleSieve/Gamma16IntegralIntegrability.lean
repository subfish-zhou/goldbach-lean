import MathlibNt.Wu2008DoubleSieve.Gamma16IntegralEnvelope

/-!
# Integrability of every literal fourfold fibre

A continuous clipped extension equals the literal kernel on every closed
source fibre. Thus none of the integral identities uses a default value
for a nonintegrable function.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

noncomputable def gamma16FullExtension (φ w t u v : ℝ) : ℝ :=
  buchstab ((φ - gamma16Clip t - gamma16Clip u - gamma16Clip v - gamma16Clip w) /
    gamma16Clip v) /
    (gamma16Clip t * gamma16Clip u * gamma16Clip v ^ 2 * gamma16Clip w)

theorem gamma16_full_extension_continuous (φ : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ => gamma16FullExtension φ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hc : Continuous gamma16Clip := continuous_const.max (continuous_const.min continuous_id)
  have hw := hc.comp (continuous_fst : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.1))
  have ht := hc.comp (show Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) by fun_prop)
  have hu := hc.comp (show Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) by fun_prop)
  have hv := hc.comp (show Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) by fun_prop)
  have hp (x : ℝ) : 0 < gamma16Clip x := by linarith [gamma16_constants.1, (gamma16_clip_mem x).1]
  exact (continuous_buchstab.comp
    ((((continuous_const.sub ht).sub hu).sub hv).sub hw |>.div hv (fun p => (hp p.2.2.2).ne'))).div
    (((ht.mul hu).mul (hv.pow 2)).mul hw) (fun p =>
      (mul_pos (mul_pos (mul_pos (hp p.2.1) (hp p.2.2.1))
        (sq_pos_of_pos (hp p.2.2.2))) (hp p.1)).ne')

theorem gamma16_full_extension_eq {φ w t u v : ℝ}
    (hw : w ∈ Icc gamma16Alpha gamma16Beta)
    (ht : t ∈ Icc gamma16Alpha w) (hu : u ∈ Icc t w) (hv : v ∈ Icc u w) :
    gamma16FullExtension φ w t u v =
      buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w) := by
  simp only [gamma16FullExtension, gamma16_clip_eq hw,
    gamma16_clip_eq ⟨ht.1, ht.2.trans hw.2⟩,
    gamma16_clip_eq ⟨ht.1.trans hu.1, hu.2.trans hw.2⟩,
    gamma16_clip_eq ⟨(ht.1.trans hu.1).trans hv.1, hv.2.trans hw.2⟩]

private theorem moving_continuous {X : Type*} [TopologicalSpace X]
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

noncomputable def gamma16InnerExtension (φ w t u : ℝ) : ℝ :=
  ∫ v in u..w, gamma16FullExtension φ w t u v

noncomputable def gamma16MiddleExtension (φ w t : ℝ) : ℝ :=
  ∫ u in t..w, gamma16InnerExtension φ w t u

noncomputable def gamma16OuterExtension (φ w : ℝ) : ℝ :=
  ∫ t in gamma16Alpha..w, gamma16MiddleExtension φ w t

theorem gamma16_inner_extension_continuous (φ : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ => gamma16InnerExtension φ p.1 p.2.1 p.2.2) := by
  apply moving_continuous (X := ℝ × ℝ × ℝ)
    (l := fun p => p.2.2) (h := fun p => p.1)
    (f := fun p v => gamma16FullExtension φ p.1 p.2.1 p.2.2 v)
  · exact (gamma16_full_extension_continuous φ).comp
      (f := fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.1, p.1.2.2, p.2))
      (show Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.1, p.1.2.2, p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem gamma16_middle_extension_continuous (φ : ℝ) :
    Continuous (fun p : ℝ × ℝ => gamma16MiddleExtension φ p.1 p.2) := by
  apply moving_continuous (X := ℝ × ℝ)
    (l := fun p => p.2) (h := fun p => p.1)
    (f := fun p u => gamma16InnerExtension φ p.1 p.2 u)
  · exact (gamma16_inner_extension_continuous φ).comp
      (f := fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2))
      (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem gamma16_outer_extension_continuous (φ : ℝ) :
    Continuous (gamma16OuterExtension φ) := by
  apply moving_continuous (X := ℝ)
    (l := fun _ => gamma16Alpha) (h := id) (f := fun w t => gamma16MiddleExtension φ w t)
  · exact gamma16_middle_extension_continuous φ
  · fun_prop
  · fun_prop

theorem gamma16_inner_extension_eq {φ w t u : ℝ}
    (hw : w ∈ Icc gamma16Alpha gamma16Beta)
    (ht : t ∈ Icc gamma16Alpha w) (hu : u ∈ Icc t w) :
    gamma16InnerExtension φ w t u =
      ∫ v in u..w, buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w) := by
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu.2] at hv
  exact gamma16_full_extension_eq hw ht hu hv

theorem gamma16_middle_extension_eq {φ w t : ℝ}
    (hw : w ∈ Icc gamma16Alpha gamma16Beta) (ht : t ∈ Icc gamma16Alpha w) :
    gamma16MiddleExtension φ w t =
      ∫ u in t..w, ∫ v in u..w, buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht.2] at hu
  exact gamma16_inner_extension_eq hw ht hu

theorem gamma16_outer_extension_eq {φ w : ℝ}
    (hw : w ∈ Icc gamma16Alpha gamma16Beta) :
    gamma16OuterExtension φ w =
      ∫ t in gamma16Alpha..w, ∫ u in t..w, ∫ v in u..w,
        buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w) := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hw.1] at ht
  exact gamma16_middle_extension_eq hw ht

theorem gamma16_literal_fibres_integrable (φ : ℝ) :
    (∀ w ∈ Icc gamma16Alpha gamma16Beta, ∀ t ∈ Icc gamma16Alpha w, ∀ u ∈ Icc t w,
      IntervalIntegrable (fun v =>
        buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w)) volume u w) ∧
    (∀ w ∈ Icc gamma16Alpha gamma16Beta, ∀ t ∈ Icc gamma16Alpha w,
      IntervalIntegrable (fun u => ∫ v in u..w,
        buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w)) volume t w) ∧
    (∀ w ∈ Icc gamma16Alpha gamma16Beta,
      IntervalIntegrable (fun t => ∫ u in t..w, ∫ v in u..w,
        buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w)) volume gamma16Alpha w) ∧
    IntervalIntegrable (fun w => ∫ t in gamma16Alpha..w, ∫ u in t..w, ∫ v in u..w,
      buchstab ((φ - t - u - v - w) / v) / (t * u * v ^ 2 * w))
      volume gamma16Alpha gamma16Beta := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw t ht u hu
    have hc := (gamma16_full_extension_continuous φ).comp
      (f := fun v : ℝ => (w, t, u, v))
      (show Continuous (fun v : ℝ => (w, t, u, v)) by fun_prop)
    apply ContinuousOn.intervalIntegrable
    apply hc.continuousOn.congr
    intro v hv
    rw [uIcc_of_le hu.2] at hv
    exact (gamma16_full_extension_eq hw ht hu hv).symm
  · intro w hw t ht
    have hc := (gamma16_inner_extension_continuous φ).comp
      (f := fun u : ℝ => (w, t, u))
      (show Continuous (fun u : ℝ => (w, t, u)) by fun_prop)
    apply ContinuousOn.intervalIntegrable
    apply hc.continuousOn.congr
    intro u hu
    rw [uIcc_of_le ht.2] at hu
    exact (gamma16_inner_extension_eq hw ht hu).symm
  · intro w hw
    have hc := (gamma16_middle_extension_continuous φ).comp
      (f := fun t : ℝ => (w, t))
      (show Continuous (fun t : ℝ => (w, t)) by fun_prop)
    apply ContinuousOn.intervalIntegrable
    apply hc.continuousOn.congr
    intro t ht
    rw [uIcc_of_le hw.1] at ht
    exact (gamma16_middle_extension_eq hw ht).symm
  · apply ContinuousOn.intervalIntegrable
    apply (gamma16_outer_extension_continuous φ).continuousOn.congr
    intro w hw
    rw [uIcc_of_le gamma16_constants.2.1] at hw
    exact (gamma16_outer_extension_eq hw).symm

end Wu2008DoubleSieve
