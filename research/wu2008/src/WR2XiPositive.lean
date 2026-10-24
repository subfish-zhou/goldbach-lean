import WR2XiOriginalFeedback

/-! Positivity of the original second kernel through its integral representation. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem originalJ_nonneg {f : ℝ → ℝ} (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t)
    {r S : ℝ} (hr : 2 ≤ r) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hrS : r < S) (hrr : 2 ≤ S - S/r) : 0 ≤ originalJ f r S := by
  obtain ⟨ha, hab, hb, hlo, hhi⟩ := J_endpoints hr hS hS5 hrS hrr
  apply intervalIntegral.integral_nonneg hab.le
  intro u hu
  have hS0 : 0 ≤ S := by linarith
  have hmullo := mul_le_mul_of_nonneg_right hu.1 hS0
  have hmulhi := mul_le_mul_of_nonneg_right hu.2 hS0
  apply div_nonneg
  · exact (profiles_nonneg hf).2.1 _ ⟨by nlinarith, by nlinarith⟩
  · exact mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])

theorem original66_nonneg {f : ℝ → ℝ} (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    0 ≤ original66 f p := by
  rcases hp with ⟨hs, _, hS, hS5, hs3, h32, h21, h1S, _, ha, _⟩
  have hk : 0 < p.kappa2 := by linarith
  have hS0 : 0 < p.S := by linarith
  have hlo := (ha 5).1
  change 1 ≤ p.S - 2*p.S/p.kappa2 at hlo
  apply intervalIntegral.integral_nonneg (one_div_le_one_div_of_le hk (by linarith))
  intro x hx
  have hx0 : 0 < x := (one_div_pos.mpr hS0).trans_le hx.1
  apply div_nonneg _ hx0.le
  apply intervalIntegral.integral_nonneg hx.2
  intro u hu
  have hb := source66_rectangle_bounds hS0 hx hu
  have harg : p.S - p.S*x - p.S*u ∈ Icc (1:ℝ) 3 := by
    constructor <;> nlinarith [hb.1, hb.2]
  apply div_nonneg (hf _ harg)
  apply mul_nonneg (by linarith [hu.1])
  nlinarith [harg.1]

theorem original67_nonneg {f : ℝ → ℝ} (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    0 ≤ original67 f p := by
  rcases hp with ⟨hs, _, hS, hS5, hs3, h32, h21, h1S, _, ha, _⟩
  have hk1 : 0 < p.kappa1 := by linarith
  have hk3 : 0 < p.kappa3 := by linarith
  have hS0 : 0 < p.S := by linarith
  have hlo := (ha 6).1
  have hhi := (ha 3).2
  change 1 ≤ p.S - p.S/p.kappa1 - p.S/p.kappa3 at hlo
  change p.S - p.S/p.kappa2 - 1 ≤ 3 at hhi
  apply intervalIntegral.integral_nonneg (one_div_le_one_div_of_le hk1 h1S)
  intro x hx
  have hx0 : 0 < x := (one_div_pos.mpr hS0).trans_le hx.1
  apply div_nonneg _ hx0.le
  apply intervalIntegral.integral_nonneg (one_div_le_one_div_of_le hk3 h32.le)
  intro u hu
  have hb := source67_rectangle_bounds hS0 hx hu
  have harg : p.S - p.S*x - p.S*u ∈ Icc (1:ℝ) 3 := by
    constructor <;> nlinarith [hb.1, hb.2]
  apply div_nonneg (hf _ harg)
  apply mul_nonneg ((one_div_pos.mpr (by linarith : 0 < p.kappa2)).le.trans hu.1)
  nlinarith [harg.1]

theorem original68_nonneg {f : ℝ → ℝ} (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    0 ≤ original68 f p := by
  rcases hp with ⟨hs, _, hS, hS5, hs3, h32, h21, h1S, _, ha, _⟩
  have hk1 : 0 < p.kappa1 := by linarith
  have hk2 : 0 < p.kappa2 := by linarith
  have hS0 : 0 < p.S := by linarith
  have hlo := (ha 8).1
  change 1 ≤ p.kappa1 - p.kappa1/p.kappa2 - 1 at hlo
  apply intervalIntegral.integral_nonneg (one_div_le_one_div_of_le hk1 h1S)
  intro x hx
  have hx0 : 0 < x := (one_div_pos.mpr hS0).trans_le hx.1
  apply div_nonneg _ hx0.le
  have hxu := hx.2.trans (one_div_le_one_div_of_le hk2 h21.le)
  apply intervalIntegral.integral_nonneg hxu
  intro u hu
  have hb := source68_rectangle_bounds hS0 hk1 (by linarith) hx hu
  have harg : (1-x-u)/x ∈ Icc (1:ℝ) 3 := ⟨hlo.trans hb.1, by linarith [hb.2]⟩
  apply div_nonneg (hf _ harg)
  apply mul_nonneg (by linarith [hu.1])
  have h := (le_div_iff₀ hx0).mp harg.1
  linarith

/-- Positivity follows from the original integrals, without expanding the logarithmic kernel. -/
theorem Xi2_integral_nonneg {f : ℝ → ℝ}
    (hi : IntervalIntegrable f volume 1 3) (hf : ∀ t ∈ Icc (1:ℝ) 3, 0 ≤ f t)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    0 ≤ ∫ t in (1:ℝ)..3, f t * Xi2 p t := by
  rw [Xi2_original_identity hi hp]
  obtain ⟨hs, hS, hS5, hk1, hk2, hk3, hsS, h2S, h3S, hr2, hr3⟩ :=
    second_parameter_bounds hp
  have hj1 := originalJ_nonneg hf hs hS hS5 hsS hp.2.2.2.2.2.2.2.2.1
  have hj2 := originalJ_nonneg hf hk2 hS hS5 h2S hr2
  have hj3 := originalJ_nonneg hf hk3 hS hS5 h3S hr3
  have he1 := (profiles_nonneg hf).2.2 p.S ⟨hS, hS5⟩
  have he2 := (profiles_nonneg hf).2.2 p.kappa1 ⟨hk1, hp.2.2.2.2.2.2.2.1.trans hS5⟩
  have h66 := original66_nonneg hf hp
  have h67 := original67_nonneg hf hp
  have h68 := original68_nonneg hf hp
  positivity

/-- Integral comparison needs positivity on the source interval only. -/
theorem Xi2_integral_mono {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) (hg : IntervalIntegrable g volume 1 3)
    (hfg : ∀ t ∈ Icc (1:ℝ) 3, f t ≤ g t)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1:ℝ)..3, f t * Xi2 p t) ≤ ∫ t in (1:ℝ)..3, g t * Xi2 p t := by
  have h := Xi2_integral_nonneg (hg.sub hf) (fun t ht => sub_nonneg.mpr (hfg t ht)) hp
  simp only [sub_mul] at h
  rw [intervalIntegral.integral_sub (Xi2_integrable hg hp) (Xi2_integrable hf hp)] at h
  exact sub_nonneg.mp h

theorem Xi2_actual_integral_nonneg {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    0 ≤ ∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 p t := by
  have hhalf : δ < 1/2 := by linarith
  apply Xi2_integral_nonneg
    (wuImprovementLimit_intervalIntegrable true hd hhalf
      (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)) _ hp
  intro t ht
  exact wuImprovementLimit_nonneg true hd hhalf ht.1 (ht.2.trans (by norm_num))

end WuPaper.R2Xi
