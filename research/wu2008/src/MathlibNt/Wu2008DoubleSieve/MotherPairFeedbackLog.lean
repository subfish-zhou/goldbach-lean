import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackTransport

/-! Independently evaluable logarithmic sections, clipped at empty bands. -/
namespace Wu2008DoubleSieve.MotherPair
open Set Real MeasureTheory
open scoped Classical Topology Interval

noncomputable def feedbackPole (p : SecondFunctionalParameters) : Term → ℝ → ℝ
  | .gammaFive, v => 1-v/p.S
  | .gammaSix, v => 1-v/p.S
  | .gammaSeven, v => 1/(v+1)
  | .gammaEight, v => 1/(v+1)

noncomputable def feedbackFactor (p : SecondFunctionalParameters) : Term → ℝ → ℝ
  | .gammaFive, v => 1/(v*(1-v/p.S))
  | .gammaSix, v => 1/(v*(1-v/p.S))
  | .gammaSeven, v => 1/v
  | .gammaEight, v => 1/v

noncomputable def feedbackLogKernel (p : SecondFunctionalParameters) (j : Term) (v : ℝ) : ℝ :=
  if v ∈ Icc 1 3 ∧ feedbackLower p j v < feedbackUpper p j v then
    feedbackFactor p j v * log
      (feedbackUpper p j v * (feedbackPole p j v-feedbackLower p j v) /
        (feedbackLower p j v * (feedbackPole p j v-feedbackUpper p j v)))
  else 0

theorem feedback_pole_geometry {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {v t : ℝ} (hv : v ∈ Icc 1 3)
    (ht : t ∈ Icc (feedbackLower p j v) (feedbackUpper p j v)) :
    0 < t ∧ t < feedbackPole p j v := by
  have hr := (feedback_section_iff h j hv t).mpr ht
  obtain ⟨hAt,_,htu,_⟩ := pairRegion_bounds h j hr.1
  have ht0 : 0 < t := by have := (gain_endpoint_order h j).1; linarith
  have hu0 : 0 < feedbackU p j v t := ht0.trans_le htu
  have hv1 : 0 < v+1 := by linarith [hv.1]
  refine ⟨ht0,?_⟩
  cases j <;> dsimp [feedbackPole,feedbackU,feedbackJac] at hu0 ⊢
  · rw [one_div_mul_eq_div] at hu0
    linarith
  · rw [one_div_mul_eq_div] at hu0
    linarith
  · apply (lt_div_iff₀ hv1).mpr
    nlinarith
  · apply (lt_div_iff₀ hv1).mpr
    nlinarith

theorem feedback_fixed_factor {q : ℝ} (hq : q ≠ 0) (v t : ℝ) :
    1/(v*t*(q-t)) = 1/(v*q)*firstFeedbackWeightedKernel q t := by
  dsimp [firstFeedbackWeightedKernel]
  field_simp

theorem feedback_density_weighted {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {v t : ℝ} (hv : v ∈ Icc 1 3)
    (ht : t ∈ Icc (feedbackLower p j v) (feedbackUpper p j v)) :
    feedbackDensity p j v t =
      feedbackFactor p j v * firstFeedbackWeightedKernel (feedbackPole p j v) t := by
  have hg := feedback_pole_geometry h j hv ht
  have hP : feedbackPole p j v ≠ 0 := ne_of_gt (hg.1.trans hg.2)
  have ht0 := hg.1.ne'
  have hv0 : v ≠ 0 := ne_of_gt (by linarith [hv.1])
  have hv1 : v+1 ≠ 0 := ne_of_gt (by linarith [hv.1])
  have hS : p.S ≠ 0 := ne_of_gt (by linarith [h.three_le_S])
  cases j with
  | gammaFive =>
    rw [feedback_density_fixed p .gammaFive (Or.inl rfl) hS]
    exact feedback_fixed_factor hP v t
  | gammaSix =>
    rw [feedback_density_fixed p .gammaSix (Or.inr rfl) hS]
    exact feedback_fixed_factor hP v t
  | gammaSeven =>
    rw [feedback_density_selected p .gammaSeven (Or.inl rfl) ht0]
    dsimp [feedbackFactor,feedbackPole,firstFeedbackWeightedKernel]
    field_simp
  | gammaEight =>
    rw [feedback_density_selected p .gammaEight (Or.inr rfl) ht0]
    dsimp [feedbackFactor,feedbackPole,firstFeedbackWeightedKernel]
    field_simp

theorem feedback_kernel_log {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (v : ℝ) : feedbackKernel p j v = feedbackLogKernel p j v := by
  by_cases hv : v ∈ Icc 1 3
  · rw [feedback_kernel_section h j hv]
    by_cases hLU : feedbackLower p j v < feedbackUpper p j v
    · rw [if_pos hLU,feedbackLogKernel,if_pos ⟨hv,hLU⟩]
      have hL := feedback_pole_geometry h j hv ⟨le_rfl,hLU.le⟩
      have hU := feedback_pole_geometry h j hv ⟨hLU.le,le_rfl⟩
      calc
        _ = ∫ t in (feedbackLower p j v)..(feedbackUpper p j v),
            feedbackFactor p j v * firstFeedbackWeightedKernel (feedbackPole p j v) t := by
          apply intervalIntegral.integral_congr
          intro t ht
          apply feedback_density_weighted h j hv
          simpa only [uIcc_of_le hLU.le] using ht
        _ = _ := by
          rw [intervalIntegral.integral_const_mul,
            firstFeedbackWeightedKernel_integral hL.1 hLU.le hU.2]
    · simp only [feedbackLogKernel,hv,hLU,and_false,if_false]
  · have he : feedbackKernel p j v = 0 := by
      by_contra he
      exact hv (feedback_kernel_support h j he)
    simp only [he,feedbackLogKernel,hv,false_and,if_false]

theorem feedback_log_measurable (p : SecondFunctionalParameters) (j : Term) :
    Measurable (feedbackLogKernel p j) := by
  have hL : Measurable (feedbackLower p j) := by
    change Measurable (fun v => feedbackLower p j v)
    cases j <;> dsimp [feedbackLower] <;> fun_prop
  have hU : Measurable (feedbackUpper p j) := by
    change Measurable (fun v => feedbackUpper p j v)
    cases j <;> dsimp [feedbackUpper] <;> fun_prop
  have hP : Measurable (feedbackPole p j) := by
    change Measurable (fun v => feedbackPole p j v)
    cases j <;> dsimp [feedbackPole] <;> fun_prop
  have hF : Measurable (feedbackFactor p j) := by
    change Measurable (fun v => feedbackFactor p j v)
    cases j <;> dsimp [feedbackFactor] <;> fun_prop
  exact (hF.mul ((hU.mul (hP.sub hL)).div (hL.mul (hP.sub hU))).log).ite
    (measurableSet_Icc.inter (measurableSet_lt hL hU)) measurable_const

theorem feedback_kernel_measurable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : Measurable (feedbackKernel p j) := by
  have he : feedbackKernel p j = feedbackLogKernel p j := funext (feedback_kernel_log h j)
  rw [he]
  exact feedback_log_measurable p j

theorem feedback_log_nonnegative {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (v : ℝ) : 0 ≤ feedbackLogKernel p j v := by
  rw [← feedback_kernel_log h j]
  exact feedback_kernel_nonnegative h j v

theorem feedback_log_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : Integrable (feedbackLogKernel p j) := by
  have he : feedbackKernel p j = feedbackLogKernel p j := funext (feedback_kernel_log h j)
  rw [← he]
  exact feedback_kernel_integrable h j

/-- The original gain equals the explicit logarithmic feedback, on the full parameter domain. -/
theorem gainIntegral_feedbackLog {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral p j δ =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackLogKernel p j v := by
  rw [gainIntegral_feedback h j hδ hδhi]
  simp_rw [feedback_kernel_log h j]

end Wu2008DoubleSieve.MotherPair
