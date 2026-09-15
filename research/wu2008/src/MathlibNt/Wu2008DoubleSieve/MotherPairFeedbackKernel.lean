import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackGeometry
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackKernel

/-! The actual inverse-Jacobian density, independent of the improvement function. -/
namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def feedbackDensity (p : SecondFunctionalParameters) (j : Term) (v t : ℝ) : ℝ :=
  feedbackJac p j t / (t*feedbackU p j v t*(1-t-feedbackU p j v t))

noncomputable def feedbackMasked (p : SecondFunctionalParameters) (j : Term) (v t : ℝ) : ℝ :=
  if (t,feedbackU p j v t) ∈ gainRegion p j then feedbackDensity p j v t else 0

/-- A genuine one-coordinate section, not a constant made from the source integral. -/
noncomputable def feedbackKernel (p : SecondFunctionalParameters) (j : Term) (v : ℝ) : ℝ :=
  ∫ t : ℝ, feedbackMasked p j v t

theorem feedback_density_fixed (p : SecondFunctionalParameters) (j : Term)
    (hj : j = .gammaFive ∨ j = .gammaSix) (hS : p.S ≠ 0) (v t : ℝ) :
    feedbackDensity p j v t = 1/(v*t*(1-v/p.S-t)) := by
  rcases hj with rfl | rfl <;> dsimp [feedbackDensity,feedbackU,feedbackJac] <;>
    field_simp <;> ring

theorem feedback_density_selected (p : SecondFunctionalParameters) (j : Term)
    (hj : j = .gammaSeven ∨ j = .gammaEight) {t : ℝ} (ht : t ≠ 0) (v : ℝ) :
    feedbackDensity p j v t = 1/(v*t*(1-(v+1)*t)) := by
  have he : t*(1-t-t*v)*(1-t-(1-t-t*v)) =
      t*(v*t*(1-(v+1)*t)) := by ring
  rcases hj with rfl | rfl <;> dsimp [feedbackDensity,feedbackU,feedbackJac] <;>
    rw [he, div_mul_cancel_left₀ ht, one_div]

theorem feedback_masked_measurable (p : SecondFunctionalParameters) (j : Term) :
    Measurable (fun z : ℝ × ℝ => feedbackMasked p j z.1 z.2) := by
  have hj : Measurable (fun z : ℝ × ℝ => feedbackJac p j z.2) := by
    cases j <;> dsimp [feedbackJac] <;> fun_prop
  have hu : Measurable (fun z : ℝ × ℝ => feedbackU p j z.1 z.2) := by
    exact (measurable_const.sub measurable_snd).sub (hj.mul measurable_fst)
  exact (hj.div ((measurable_snd.mul hu).mul
    ((measurable_const.sub measurable_snd).sub hu))).ite
      ((gain_region_measurable p j).preimage (measurable_snd.prodMk hu)) measurable_const

theorem feedback_masked_support {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : Function.support (fun z : ℝ × ℝ => feedbackMasked p j z.1 z.2) ⊆
      Icc (1:ℝ) 3 ×ˢ Icc (1/p.S) (1/p.kappa3) := by
  intro z hz
  have hr : (z.2,feedbackU p j z.1 z.2) ∈ gainRegion p j := by
    by_contra hn
    exact hz (if_neg hn)
  have ht := ((pairRegion_iff h j _ _).mp hr.1).1
  have hv := gain_ratio_mem h j hr
  rw [feedback_inverse_ratio h j ht] at hv
  exact ⟨hv,ht.1,ht.2.trans (gain_endpoint_order h j).2.2.1⟩

theorem feedback_masked_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (v t : ℝ) :
    0 ≤ feedbackMasked p j v t ∧
      feedbackMasked p j v t ≤ 25/(1-2*(1/p.kappa3)) := by
  have hg : 0 < 1-2*(1/p.kappa3) := by
    have := (gain_endpoint_order h j).2.2.2.2.2.2
    linarith
  unfold feedbackMasked
  split_ifs with hr
  · have ht := ((pairRegion_iff h j _ _).mp hr.1).1
    have hJ := feedback_jac_bounds h j ht
    have hd := pair_denominator_bound h j hr.1
    refine ⟨div_nonneg hJ.1.le hd.1.le, ?_⟩
    exact (div_le_div₀ (by norm_num) hJ.2 (mul_pos (by norm_num) hg) hd.2).trans_eq
      (by field_simp)
  · exact ⟨le_rfl,by positivity⟩

theorem feedback_weighted_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun z : ℝ × ℝ => H z.1 * feedbackMasked p j z.1 z.2) := by
  have hs : Function.support (fun z : ℝ × ℝ => H z.1 * feedbackMasked p j z.1 z.2) ⊆
      Icc (1:ℝ) 3 ×ˢ Icc (1/p.S) (1/p.kappa3) := by
    intro z hz
    apply feedback_masked_support h j
    intro he
    exact hz (by simp only [he,mul_zero])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    ((hm.comp measurable_fst).mul (feedback_masked_measurable p j)).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  change ‖H z.1 * feedbackMasked p j z.1 z.2‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (feedback_masked_bounds h j z.1 z.2).1]
  exact (mul_le_mul_of_nonneg_right (hb z.1) (feedback_masked_bounds h j z.1 z.2).1).trans
    (by simpa only [one_mul] using (feedback_masked_bounds h j z.1 z.2).2)

theorem feedback_masked_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : Integrable (fun z : ℝ × ℝ => feedbackMasked p j z.1 z.2) := by
  simpa only [one_mul] using feedback_weighted_integrable h j
    (H := fun _ => 1) measurable_const (fun _ => by norm_num)

theorem feedback_kernel_nonnegative {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (v : ℝ) : 0 ≤ feedbackKernel p j v :=
  integral_nonneg (fun t => (feedback_masked_bounds h j v t).1)

theorem feedback_kernel_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : Integrable (feedbackKernel p j) :=
  (feedback_masked_integrable h j).integral_prod_left

theorem feedback_kernel_weighted_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun v => H v * feedbackKernel p j v) := by
  have hi := (feedback_weighted_integrable h j hm hb).integral_prod_left
  simpa only [integral_const_mul,feedbackKernel] using hi

/-- Closed max/min sections, with the zero-width case evaluated exactly. -/
theorem feedback_kernel_section {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {v : ℝ} (hv : v ∈ Icc 1 3) :
    feedbackKernel p j v =
      if feedbackLower p j v < feedbackUpper p j v then
        ∫ t in (feedbackLower p j v)..(feedbackUpper p j v), feedbackDensity p j v t
      else 0 := by
  unfold feedbackKernel feedbackMasked
  simp_rw [feedback_section_iff h j hv, mem_Icc]
  split_ifs with hLU
  · exact gamma5Feedback_mask_interval _ hLU.le
  · exact gamma5Feedback_mask_zero _ (le_of_not_gt hLU)

end Wu2008DoubleSieve.MotherPair
