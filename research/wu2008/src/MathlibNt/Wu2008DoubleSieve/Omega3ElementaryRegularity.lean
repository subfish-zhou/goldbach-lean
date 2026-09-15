import MathlibNt.Wu2008DoubleSieve.Omega3ElementaryMass

namespace Wu2008DoubleSieve.Omega3ElementaryRegularity
open Set MeasureTheory

/-- Only a regularity extension; it is removed on every actual closed fibre. -/
noncomputable def extension (a b c : ℝ) : ℝ :=
  1 / (max (1/10) a * (max (1/10) b)^2 * max (1/10) c)

theorem extension_continuous : Continuous (fun p : ℝ × ℝ × ℝ =>
    extension p.1 p.2.1 p.2.2) := by
  unfold extension
  fun_prop (disch := intro p; positivity)

theorem extension_eq {a b c : ℝ} (ha : 1/10 ≤ a) (hb : 1/10 ≤ b) (hc : 1/10 ≤ c) :
    extension a b c = 1/(a*b^2*c) := by
  simp only [extension, max_eq_right ha, max_eq_right hb, max_eq_right hc]

theorem continuous_moving {X : Type*} [TopologicalSpace X]
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

theorem inner_continuous (h : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ c in p.2..h, extension p.1 p.2 c) := by
  apply continuous_moving
  · exact extension_continuous.comp
      (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem middle_continuous (h : ℝ) :
    Continuous (fun a : ℝ => ∫ b in a..h, ∫ c in b..h, extension a b c) := by
  apply continuous_moving
  · exact inner_continuous h
  · fun_prop
  · fun_prop

theorem inner_eq {a b h : ℝ} (ha : 1/10 ≤ a) (hb : 1/10 ≤ b) (hbh : b ≤ h) :
    (∫ c in b..h, extension a b c) = ∫ c in b..h, 1/(a*b^2*c) := by
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hbh] at hc
  exact extension_eq ha hb (hb.trans hc.1)

theorem middle_eq {a h : ℝ} (ha : 1/10 ≤ a) (hah : a ≤ h) :
    (∫ b in a..h, ∫ c in b..h, extension a b c) =
      ∫ b in a..h, ∫ c in b..h, 1/(a*b^2*c) := by
  apply intervalIntegral.integral_congr
  intro b hb
  rw [uIcc_of_le hah] at hb
  exact inner_eq ha (ha.trans hb.1) hb.2

theorem kernel_integrable {a b h : ℝ} (ha : 1/10 ≤ a) (hb : 1/10 ≤ b) (hbh : b ≤ h) :
    IntervalIntegrable (fun c => (1 : ℝ)/(a*b^2*c)) volume b h := by
  apply ContinuousOn.intervalIntegrable
  have hc := extension_continuous.comp
    (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)
  apply hc.continuousOn.congr
  intro c hc
  rw [uIcc_of_le hbh] at hc
  exact (extension_eq ha hb (hb.trans hc.1)).symm

theorem inner_integrable {a h : ℝ} (ha : 1/10 ≤ a) (hah : a ≤ h) :
    IntervalIntegrable (fun b => ∫ c in b..h, (1 : ℝ)/(a*b^2*c)) volume a h := by
  apply ContinuousOn.intervalIntegrable
  have hc := (inner_continuous h).comp
    (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
  apply hc.continuousOn.congr
  intro b hb
  rw [uIcc_of_le hah] at hb
  exact (inner_eq ha (ha.trans hb.1) hb.2).symm

theorem middle_integrable {l h : ℝ} (hl : 1/10 ≤ l) (hlh : l ≤ h) :
    IntervalIntegrable (fun a => ∫ b in a..h, ∫ c in b..h, (1 : ℝ)/(a*b^2*c)) volume l h := by
  apply ContinuousOn.intervalIntegrable
  apply (middle_continuous h).continuousOn.congr
  intro a ha
  rw [uIcc_of_le hlh] at ha
  exact (middle_eq (hl.trans ha.1) ha.2).symm

end Wu2008DoubleSieve.Omega3ElementaryRegularity
