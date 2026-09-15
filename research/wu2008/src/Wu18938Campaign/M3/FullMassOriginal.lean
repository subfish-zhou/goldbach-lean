import Wu18938Campaign.M3.FullMassApprox
import WR2XiOriginalFeedback

noncomputable section

namespace Wu18938Campaign.M3

open Set Real MeasureTheory Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair WuPaper.R2Gamma5
open scoped Classical Interval

private theorem domain_measurable (p : SecondFunctionalParameters) :
    MeasurableSet (fullDomain p) := by
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

private theorem kernel_measurable {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Measurable (fullKernel p δ) :=
  (((gamma5Gain_H_antitone hδ hδhi).measurable.comp (by fun_prop)).mul
    (gain_smooth_continuous hp.toAnalyticParameters).measurable).indicator
      (domain_measurable p)

private theorem kernel_bounds {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (v : ℝ × ℝ) :
    0 ≤ fullKernel p δ v ∧
      fullKernel p δ v ≤ 25 / (1 - 2 * (1 / p.kappa3)) := by
  have hk := gain_smooth_bounds hp.toAnalyticParameters v
  by_cases hv : v ∈ fullDomain p
  · rw [fullKernel, indicator_of_mem hv]
    have hh := gamma5Gain_H_bounds hδ hδhi (p.S * (1 - v.1 - v.2))
    exact ⟨mul_nonneg hh.1 hk.1, (mul_le_of_le_one_left hk.1 hh.2).trans hk.2⟩
  · rw [fullKernel, indicator_of_notMem hv]
    exact ⟨le_rfl, hk.1.trans hk.2⟩

private theorem kernel_support (p : SecondFunctionalParameters) (δ : ℝ) :
    Function.support (fullKernel p δ) ⊆
      Icc (1 / p.S) (1 / p.kappa2) ×ˢ Icc (1 / p.S) (1 / p.kappa2) := by
  intro v hv
  by_cases h : v ∈ fullDomain p
  · exact ⟨⟨h.1, h.2.1.trans h.2.2⟩, ⟨h.1.trans h.2.1, h.2.2⟩⟩
  · exact False.elim (hv (indicator_of_notMem h _))

theorem full_kernel_integrable {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Integrable (fullKernel p δ) := by
  apply (integrableOn_iff_integrable_of_support_subset (kernel_support p δ)).mp
  apply Measure.integrableOn_of_bounded
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (kernel_measurable hp hδ hδhi).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (kernel_bounds hp hδ hδhi v).1]
      using (kernel_bounds hp hδ hδhi v).2)

theorem fullIntegral_eq_original66 {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    fullIntegral p δ = WuPaper.R2Xi.original66 (wuImprovementLimit true δ) p := by
  have he := parameter_order hp.toAnalyticParameters
  have hab : 1 / p.S ≤ 1 / p.kappa2 := he.2.1.trans he.2.2.1.le
  have houter : Function.support (fun t => ∫ u, fullKernel p δ (t, u)) ⊆
      Icc (1 / p.S) (1 / p.kappa2) := by
    intro t ht
    by_contra hn
    apply ht
    have hz : (fun u => fullKernel p δ (t, u)) = 0 := by
      funext u
      have hv : (t, u) ∉ fullDomain p :=
        fun h => hn ⟨h.1, h.2.1.trans h.2.2⟩
      exact indicator_of_notMem hv _
    rw [hz]
    exact integral_zero
  have hinner (t : ℝ) : Function.support (fun u => fullKernel p δ (t, u)) ⊆
      Icc t (1 / p.kappa2) := by
    intro u hu
    by_cases hv : (t, u) ∈ fullDomain p
    · exact ⟨hv.2.1, hv.2.2⟩
    · exact False.elim (hu (indicator_of_notMem hv _))
  unfold fullIntegral WuPaper.R2Xi.original66
  rw [show (∫ v : ℝ × ℝ, fullKernel p δ v) =
    ∫ t, ∫ u, fullKernel p δ (t, u) from
      integral_prod _ (full_kernel_integrable hp hδ hδhi),
    truncatedSixthMass_integral_eq_interval hab houter]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa2) := by
    simpa only [uIcc_of_le hab] using ht
  rw [truncatedSixthMass_integral_eq_interval ht'.2 (hinner t),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc t (1 / p.kappa2) := by
    simpa only [uIcc_of_le ht'.2] using hu
  rw [full_kernel_value hp δ ⟨ht'.1, hu'.1, hu'.2⟩,
    show p.S * (1 - t - u) = p.S - p.S * t - p.S * u by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem fullHMass_original66_lower {p : SecondFunctionalParameters} (hp : FullParameters p)
    (k : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (WuPaper.R2Xi.original66 (wuImprovementLimit true δ) p - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          fullHMass p N δ (convolutionWuWindows N Δ V)
            (termLabels p .gammaFive N δ (convolutionWuWindows N Δ V)) := by
  simpa only [fullIntegral_eq_original66 hp hδ (by linarith : δ < 1 / 2)] using
    fullHMass_integral_lower hp k hδ hδhi hε

end Wu18938Campaign.M3
