import MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegral

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open LiLiuGoldbachIdealPairKernel

noncomputable section
namespace G67ElementaryIntegral

/-- Continuity on the full compact domain of the two actual integrals. -/
theorem weighted_continuousOn : ContinuousOn
    (fun x : ℝ × ℝ => elementaryKernel x / (x.1*x.2))
    (Icc (4/53 : ℝ) (4/33 : ℝ) ×ˢ Icc (4/53 : ℝ) (3/11 : ℝ)) := by
  have hD : Continuous (fun x : ℝ × ℝ => (1/2 : ℝ)-x.1-x.2) :=
    (continuous_const.sub continuous_fst).sub continuous_snd
  have hL : Continuous (fun x : ℝ × ℝ => ((1/2 : ℝ)-x.1-x.2-(4/53 : ℝ))/(4/53 : ℝ)) :=
    (hD.sub continuous_const).div_const _
  have hlog := (hL.continuousOn (s := Icc (4/53 : ℝ) (4/33 : ℝ) ×ˢ Icc (4/53 : ℝ) (3/11 : ℝ))).log
    (fun x hx => (domain_bounds hx.1 hx.2).2.2.2.1.ne')
  have hratio := hlog.div hD.continuousOn
    (fun x hx => (domain_bounds hx.1 hx.2).2.2.1.ne')
  have hker : ContinuousOn elementaryKernel
      (Icc (4/53 : ℝ) (4/33 : ℝ) ×ˢ Icc (4/53 : ℝ) (3/11 : ℝ)) :=
    ContinuousOn.sup continuousOn_const hratio
  exact hker.div (continuous_fst.mul continuous_snd).continuousOn
    (fun x hx => (mul_pos (domain_bounds hx.1 hx.2).1
      (domain_bounds hx.1 hx.2).2.1).ne')

/-- Actual weighted integrability, with no analytic input premises. -/
theorem weighted_integrable {c d : ℝ} (hc : (4/53 : ℝ) ≤ c) (hd : d ≤ (3/11 : ℝ)) :
    IntegrableOn (fun x : ℝ × ℝ => elementaryKernel x / (x.1*x.2))
      (Ioc (4/53 : ℝ) (4/33 : ℝ) ×ˢ Ioc c d) := by
  apply (weighted_continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro x hx
  exact ⟨⟨hx.1.1.le,hx.1.2⟩,⟨hc.trans hx.2.1.le,hx.2.2.trans hd⟩⟩

/-- The pointwise lower bound integrated over either required positive rectangle. -/
theorem rectangle_lower {c d : ℝ} (hc : (4/53 : ℝ) ≤ c)
    (hd : d ≤ (3/11 : ℝ)) (hcd : c ≤ d) :
    (2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ)) *
      (∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in c..d, elementaryKernel (u,v)/(u*v)) ≤
      ∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in c..d, kernel 0 (u,v)/(u*v) := by
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ)
  have he := weighted_integrable hc hd
  have hk := kernel_weighted_integrable 0 (b := 4/33) (d := d)
    (by norm_num : (0 : ℝ) < 4/53) (by linarith : 0 < c)
  rw [← LiLiuGoldbachLogDarboux.integral_eq_iterated (by norm_num) hcd he,
    ← LiLiuGoldbachLogDarboux.integral_eq_iterated (by norm_num) hcd hk,
    ← integral_const_mul]
  apply setIntegral_mono_on (he.const_mul A) hk (measurableSet_Ioc.prod measurableSet_Ioc)
  intro x hx
  have hu : x.1 ∈ Icc (4/53 : ℝ) (4/33 : ℝ) := ⟨hx.1.1.le,hx.1.2⟩
  have hv : x.2 ∈ Icc (4/53 : ℝ) (3/11 : ℝ) := ⟨hc.trans hx.2.1.le,hx.2.2.trans hd⟩
  have hb := kernel_lower hu hv
  have hp := domain_bounds hu hv
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb (mul_pos hp.1 hp.2.1).le

/-- A separately named auxiliary integral preserves both original domains and the half-square. -/
def elementaryIntegral : ℝ :=
  (1/2 : ℝ) * (∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in (4/53 : ℝ)..(4/33 : ℝ),
    elementaryKernel (u,v)/(u*v)) +
  (∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in (4/33 : ℝ)..(3/11 : ℝ),
    elementaryKernel (u,v)/(u*v))

/-- The actual unnormalized JR integral dominates the explicit auxiliary integral. -/
theorem actual_integral_lower :
    (2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ)) * elementaryIntegral ≤
      goldbachG67JRIntegral 0 := by
  have h6 := rectangle_lower (c := 4/53) (d := 4/33) (by norm_num) (by norm_num) (by norm_num)
  have h7 := rectangle_lower (c := 4/33) (d := 3/11) (by norm_num) (by norm_num) (by norm_num)
  unfold elementaryIntegral goldbachG67JRIntegral
  linarith

/-- The fixed actual C67 has the explicit exp-free logarithmic integral lower bound. -/
theorem actual_constant_lower : 4 * elementaryIntegral ≤ goldbachG67IntegralConstant := by
  have hE : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have h := mul_le_mul_of_nonneg_left actual_integral_lower
    (show 0 ≤ (53 : ℝ)/(2*Real.exp Real.eulerMascheroniConstant) by positivity)
  have hscale : ((53 : ℝ)/(2*Real.exp Real.eulerMascheroniConstant)) *
      (2 * Real.exp Real.eulerMascheroniConstant * (4/53 : ℝ)) = 4 := by
    field_simp
  rw [← mul_assoc, hscale] at h
  exact h

/-- Literal public endpoint: no JR function, exponential, or analytic premise on the lower side. -/
theorem actual_constant_lower_explicit :
    4 * ((1/2 : ℝ) *
      (∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in (4/53 : ℝ)..(4/33 : ℝ),
        max 0 (Real.log ((1/2-u-v-(4/53 : ℝ))/(4/53 : ℝ))/(1/2-u-v))/(u*v)) +
      (∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in (4/33 : ℝ)..(3/11 : ℝ),
        max 0 (Real.log ((1/2-u-v-(4/53 : ℝ))/(4/53 : ℝ))/(1/2-u-v))/(u*v))) ≤
      goldbachG67IntegralConstant := actual_constant_lower

end G67ElementaryIntegral
