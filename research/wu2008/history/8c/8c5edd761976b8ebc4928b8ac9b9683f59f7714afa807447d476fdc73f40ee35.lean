import SrcSixthGainSource

noncomputable section
namespace WuSource.SrcSixthGain
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High
open Wu08G6TableGeometryRecovery Wu2008DoubleSieve NodeExtension
open scoped Classical BigOperators

def envelope : Set (ℝ × ℝ) := Icc alpha beta ×ˢ Icc beta (1/2-3*alpha)
def rawMasked (S : Set (ℝ × ℝ)) (p : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ S then kernel p v.1 v.2 else 0
def denominatorFloor : ℝ := alpha*beta*(3*alpha-beta)

theorem envelope_bounds :
    alpha ≤ beta ∧ beta ≤ 1/2-2*beta ∧
      1/2-2*beta ≤ 1/2-3*alpha ∧ alpha ≤ 3*alpha/2 ∧
      3*alpha/2 ≤ beta ∧ 0 < denominatorFloor := by
  norm_num [alpha,beta,denominatorFloor]

theorem rectangleA_subset : regionA ⊆ envelope := by
  intro v hv
  exact ⟨hv.1,hv.2.1,hv.2.2.trans envelope_bounds.2.2.1⟩

theorem rectangleB_subset : regionB ⊆ envelope := by
  intro v hv
  exact ⟨⟨hv.1.1,hv.1.2.trans envelope_bounds.2.2.2.2.1⟩,
    envelope_bounds.2.1.trans hv.2.1,hv.2.2⟩

theorem published_subset : publishedReducedDomain ⊆ regionA ∪ regionB := by
  intro v hv
  have hp : v ∈ QuarterTrim.originalP := by rw [source_reduced_domain]; exact hv
  exact hp.1

theorem envelope_parameter {v : ℝ × ℝ} (hv : v ∈ envelope) :
    1 ≤ u v.1 v.2 ∧ u v.1 v.2 ≤ endpoint := by
  obtain ⟨⟨hx,hxb⟩,hy,hyt⟩ := hv
  norm_num [alpha,beta,u,endpoint] at hx hxb hy hyt ⊢
  constructor <;> linarith

theorem envelope_denominator {v : ℝ × ℝ} (hv : v ∈ envelope) :
    denominatorFloor ≤ v.1*v.2*(1/2-v.1-v.2) := by
  have hx0 := alpha_pos.le.trans hv.1.1
  have hb : 0 ≤ beta := by norm_num [beta]
  have hz : 3*alpha-beta ≤ 1/2-v.1-v.2 := by
    linarith [hv.1.2,hv.2.2]
  have hz0 : 0 ≤ 3*alpha-beta := by norm_num [alpha,beta]
  have hxy := mul_le_mul hv.1.1 hv.2.1 hb hx0
  have hh := mul_le_mul hxy hz hz0 (mul_nonneg hx0 (hb.trans hv.2.1))
  exact hh

theorem raw_integrable {p : ℝ → ℝ} {S : Set (ℝ × ℝ)} {K : ℝ}
    (hp : Measurable p) (hS : MeasurableSet S) (hsub : S ⊆ envelope)
    (hK : 0 ≤ K) (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K) :
    Integrable (rawMasked S p) := by
  have hd : 0 < denominatorFloor := envelope_bounds.2.2.2.2.2
  have hm : Measurable (fun v : ℝ × ℝ => kernel p v.1 v.2) := by
    unfold kernel u
    exact (hp.comp (by fun_prop)).div (by fun_prop)
  apply (integrable_indicator_iff hS).mpr
  apply Measure.integrableOn_of_bounded (M := K/denominatorFloor)
    (ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top)) hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hS] with v hv
  have hv' := hsub hv
  have hden := envelope_denominator hv'
  rw [Real.norm_eq_abs]
  change |p (u v.1 v.2)/(v.1*v.2*(1/2-v.1-v.2))| ≤ _
  rw [abs_div,abs_of_pos (hd.trans_le hden)]
  exact div_le_div₀ hK (hb v hv') hd hden

theorem rectangle_integral {p : ℝ → ℝ} {a b c d K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hsub : Icc a b ×ˢ Icc c d ⊆ envelope) :
    (∫ v : ℝ × ℝ, rawMasked (Icc a b ×ˢ Icc c d) p v) =
      ∫ x in a..b, ∫ y in c..d, kernel p x y := by
  have hi := raw_integrable hp (measurableSet_Icc.prod measurableSet_Icc) hsub hK hb
  rw [show (∫ v : ℝ × ℝ, rawMasked (Icc a b ×ˢ Icc c d) p v) =
      ∫ x, ∫ y, rawMasked (Icc a b ×ˢ Icc c d) p (x,y) from integral_prod _ hi]
  have hs : Function.support (fun x => ∫ y, rawMasked (Icc a b ×ˢ Icc c d) p (x,y)) ⊆
      Icc a b := by
    intro x hx
    by_contra hn
    apply hx
    have he : (fun y => rawMasked (Icc a b ×ˢ Icc c d) p (x,y)) = 0 := by
      funext y
      simp [rawMasked,hn]
    change (∫ y, rawMasked (Icc a b ×ˢ Icc c d) p (x,y)) = 0
    rw [he]
    simp
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hs' : Function.support (fun y => rawMasked (Icc a b ×ˢ Icc c d) p (x,y)) ⊆
      Icc c d := by
    intro y hy
    by_contra hn
    exact hy (by simp [rawMasked,hn])
  rw [truncatedSixthMass_integral_eq_interval hcd hs']
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hcd] at hy
  exact if_pos ⟨hx,hy⟩

theorem raw_source_integrals {p : ℝ → ℝ} {K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K) :
    paperG6 p =
      4*(∫ v : ℝ × ℝ, rawMasked regionA p v) +
      4*(∫ v : ℝ × ℝ, rawMasked regionB p v) := by
  rw [paper_eq_rectangles,
    rectangle_integral hp hK hb envelope_bounds.1 envelope_bounds.2.1 rectangleA_subset,
    rectangle_integral hp hK hb envelope_bounds.2.2.2.1 envelope_bounds.2.2.1 rectangleB_subset]
  rfl

theorem weighted_source_comparison {p : ℝ → ℝ} {w : Fin 21 → ℝ} {K : ℝ}
    (hp : Measurable p) (hK : 0 ≤ K)
    (hb : ∀ v ∈ envelope, |p (u v.1 v.2)| ≤ K)
    (hn : ∀ v ∈ envelope, 0 ≤ p (u v.1 v.2))
    (hw : ∀ v ∈ publishedReducedDomain, profile w (u v.1 v.2) ≤ p (u v.1 v.2)) :
    8*(∑ j : Fin 21, g6Weight j*w j) ≤ paperG6 p := by
  have hiA := raw_integrable hp (measurableSet_Icc.prod measurableSet_Icc) rectangleA_subset hK hb
  have hiB := raw_integrable hp (measurableSet_Icc.prod measurableSet_Icc) rectangleB_subset hK hb
  have hpos {S : Set (ℝ × ℝ)} (hsub : S ⊆ envelope) (v : ℝ × ℝ) :
      0 ≤ rawMasked S p v := by
    by_cases hv : v ∈ S
    · rw [rawMasked,if_pos hv]
      exact div_nonneg (hn v (hsub hv))
        ((envelope_bounds.2.2.2.2.2.trans_le (envelope_denominator (hsub hv))).le)
    · simp [rawMasked,hv]
  have hpoint (v : ℝ × ℝ) :
      masked publishedReducedDomain w v ≤ rawMasked regionA p v+rawMasked regionB p v := by
    by_cases hv : v ∈ publishedReducedDomain
    · have hk : kernel (profile w) v.1 v.2 ≤ kernel p v.1 v.2 :=
        div_le_div_of_nonneg_right (hw v hv) (published_denominator hv).1.le
      rw [masked,if_pos hv]
      rcases published_subset hv with ha | hb
      · rw [rawMasked,if_pos ha]
        linarith only [hk,hpos rectangleB_subset v]
      · have he : rawMasked regionB p v = kernel p v.1 v.2 := if_pos hb
        rw [he]
        linarith only [hk,hpos rectangleA_subset v]
    · rw [masked,if_neg hv]
      exact add_nonneg (hpos rectangleA_subset v) (hpos rectangleB_subset v)
  have h := integral_mono (published_integrable w) (hiA.add hiB) hpoint
  rw [integral_add hiA hiB] at h
  rw [← published_twentyone,raw_source_integrals hp hK hb]
  unfold published
  linarith only [h]

def boundedH (delta s : ℝ) : ℝ :=
  if s ≤ 2 then wuImprovementLimit false delta (max 1 (min 2 s))
  else wuImprovementLimit false delta (max 2 (min 10 s))

theorem boundedH_eq {delta s : ℝ} (hs : s ∈ Icc 1 10) :
    boundedH delta s = wuImprovementLimit false delta s := by
  by_cases h : s ≤ 2
  · simp [boundedH,h,min_eq_right h,max_eq_right hs.1]
  · simp [boundedH,h,min_eq_right hs.2,max_eq_right (le_of_not_ge h)]

theorem initial_clamp (s : ℝ) : max 1 (min 2 s) ∈ Icc (1 : ℝ) 2 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem final_clamp (s : ℝ) : max 2 (min 10 s) ∈ Icc (2 : ℝ) 10 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem boundedH_measurable {delta : ℝ} (hd : 0 < delta) (hdhi : delta ≤ 1/10) :
    Measurable (boundedH delta) := by
  have hm : Monotone (fun s => wuImprovementLimit false delta (max 1 (min 2 s))) :=
    fun s t hst => wuImprovementLimit_lower_monotone_initial hd (by linarith)
      (initial_clamp s) (initial_clamp t) (max_le_max le_rfl (min_le_min le_rfl hst))
  have ha : Antitone (fun s => wuImprovementLimit false delta (max 2 (min 10 s))) :=
    fun s t hst => wuImprovementLimit_lower_antitone hd hdhi
      (final_clamp s) (final_clamp t) (max_le_max le_rfl (min_le_min le_rfl hst))
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) hm.measurable ha.measurable

theorem boundedH_bounds {delta : ℝ} (hd : 0 < delta) (hdhi : delta ≤ 1/10) (s : ℝ) :
    0 ≤ boundedH delta s ∧ boundedH delta s ≤ wuImprovementLimit false delta 2 := by
  by_cases h : s ≤ 2
  · rw [boundedH,if_pos h]
    have hc := initial_clamp s
    exact ⟨wuImprovementLimit_nonneg false hd (by linarith) hc.1 (by linarith [hc.2]),
      wuImprovementLimit_lower_monotone_initial hd (by linarith) hc
        ⟨by norm_num,le_rfl⟩ hc.2⟩
  · rw [boundedH,if_neg h]
    have hc := final_clamp s
    exact ⟨wuImprovementLimit_nonneg false hd (by linarith) (by linarith [hc.1]) hc.2,
      wuImprovementLimit_lower_antitone hd hdhi ⟨le_rfl,by norm_num⟩ hc hc.1⟩

theorem rectangle_congr {p q : ℝ → ℝ}
    (h : ∀ v ∈ envelope, p (u v.1 v.2) = q (u v.1 v.2)) :
    paperG6 p = paperG6 q := by
  rw [paper_eq_rectangles,paper_eq_rectangles]
  unfold rectangleG6
  congr 2
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le envelope_bounds.1] at hx
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le envelope_bounds.2.1] at hy
    unfold kernel
    rw [h (x,y) (rectangleA_subset ⟨hx,hy⟩)]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le envelope_bounds.2.2.2.1] at hx
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le envelope_bounds.2.2.1] at hy
    unfold kernel
    rw [h (x,y) (rectangleB_subset ⟨hx,hy⟩)]

theorem original_whole_source_lower {w : Fin 21 → ℝ} {delta : ℝ}
    (hd : 0 < delta) (hdhi : delta ≤ 1/10)
    (hw : ∀ j, w j ≤ wuImprovementLimit false delta (rNode (j.val+1))) :
    8*(∑ j : Fin 21, g6Weight j*w j) ≤ paperG6 (wuImprovementLimit false delta) := by
  have he : paperG6 (boundedH delta) = paperG6 (wuImprovementLimit false delta) := by
    apply rectangle_congr
    intro v hv
    have hs := envelope_parameter hv
    exact boundedH_eq ⟨hs.1,hs.2.trans (by norm_num [endpoint,alpha,beta])⟩
  rw [← he]
  apply weighted_source_comparison (boundedH_measurable hd hdhi)
    (wuImprovementLimit_nonneg false hd (by linarith) (by norm_num) (by norm_num))
    (fun v _ => ?_) (fun v _ => (boundedH_bounds hd hdhi (u v.1 v.2)).1)
  · intro v hv
    have hs := envelope_parameter
      ((union_subset rectangleA_subset rectangleB_subset) (published_subset hv))
    have hs2 : 2 ≤ u v.1 v.2 := by
      apply (le_div_iff₀ alpha_pos).mpr
      linarith [hv.2.2.2]
    rw [boundedH_eq ⟨hs.1,hs.2.trans (by norm_num [endpoint,alpha,beta])⟩]
    exact profile_actual hd hdhi hw ⟨hs2,hs.2⟩
  · rw [abs_of_nonneg (boundedH_bounds hd hdhi _).1]
    exact (boundedH_bounds hd hdhi _).2

#print axioms raw_source_integrals
#print axioms weighted_source_comparison
#print axioms original_whole_source_lower
end WuSource.SrcSixthGain
