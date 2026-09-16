import Wu18938Campaign.M1.Confirmed.FullFiveActual
import Wu18938Campaign.M1.Confirmed.ProfileKernelIdentity
import WR2XiOriginalFeedback

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.PairLiteral

open Wu2008DoubleSieve MotherPair Set Real MeasureTheory Filter
open scoped Classical Interval

def kernel (p : SecondFunctionalParameters) (j : Term) (H : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  if PairRegion p j v.1 v.2 then H (Hratio p j v.1 v.2) * gainSmooth p v else 0

theorem region_measurable (p : SecondFunctionalParameters) (j : Term) :
    MeasurableSet {v : ℝ × ℝ | PairRegion p j v.1 v.2} := by
  cases j <;> unfold PairRegion <;>
    apply (measurableSet_le measurable_const measurable_fst).inter <;>
    apply (measurableSet_le measurable_fst measurable_const).inter <;>
    apply MeasurableSet.inter
  all_goals first
    | exact measurableSet_le measurable_fst measurable_snd
    | exact measurableSet_le measurable_const measurable_snd
    | exact measurableSet_le measurable_snd measurable_const

theorem kernel_integrable {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (kernel p j H) := by
  have hs : Function.support (kernel p j H) ⊆
      Icc (1 / p.S) (1 / p.kappa3) ×ˢ Icc (1 / p.S) (1 / p.kappa3) := by
    intro v hv
    have hr : PairRegion p j v.1 v.2 := by
      by_contra hn
      exact hv (if_neg hn)
    have h := pairRegion_bounds hp j hr
    exact ⟨⟨h.1,h.2.1⟩,⟨h.1.trans h.2.2.1,h.2.2.2⟩⟩
  have hmeas : Measurable (kernel p j H) :=
    ((hm.comp (gain_ratio_measurable p j)).mul (gain_smooth_continuous hp).measurable).ite
      (region_measurable p j) measurable_const
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    hmeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  change ‖kernel p j H v‖ ≤ 25 / (1 - 2 * (1 / p.kappa3))
  unfold kernel
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gain_smooth_bounds hp v).1]
    exact (mul_le_mul_of_nonneg_right (hb _) (gain_smooth_bounds hp v).1).trans
      (by simpa only [one_mul] using (gain_smooth_bounds hp v).2)
  · rw [norm_zero]
    exact (gain_smooth_bounds hp v).1.trans (gain_smooth_bounds hp v).2

theorem literal_integral {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ v : ℝ × ℝ, kernel p j H v) =
      ∫ t in (1 / p.S)..(upperP p j),
        ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
          H (Hratio p j t u) / (t * u * (1 - t - u)) := by
  have hs : Function.support (fun t => ∫ u, kernel p j H (t,u)) ⊆
      Icc (1 / p.S) (upperP p j) := by
    intro t ht
    by_contra hn
    apply ht
    have hz (u : ℝ) : kernel p j H (t,u) = 0 :=
      if_neg (fun hr => hn ((pairRegion_iff hp j t u).mp hr).1)
    simp only [hz,integral_zero]
  rw [show (∫ v : ℝ × ℝ, kernel p j H v) = ∫ t, ∫ u, kernel p j H (t,u) from
    integral_prod _ (kernel_integrable hp j hm hb),
    truncatedSixthMass_integral_eq_interval (gain_endpoint_order hp j).2.1 hs]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1 / p.S) (upperP p j) := by
    simpa only [uIcc_of_le (gain_endpoint_order hp j).2.1] using ht
  dsimp only
  have hslice : Function.support (fun u => kernel p j H (t,u)) ⊆
      Icc (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
    intro u hu
    have hr : PairRegion p j t u := by
      by_contra hn
      exact hu (if_neg hn)
    exact (pairRegion_iff_slice hp j ht' u).mp hr
  rw [truncatedSixthMass_integral_eq_interval (min_le_left _ _) hslice]
  apply intervalIntegral.integral_congr
  intro u hu
  have hr := (pairRegion_iff_slice hp j ht' u).mpr
    (by simpa only [uIcc_of_le (gain_start_bounds hp j ht').2.2] using hu)
  have hgeo := pairRegion_bounds hp j hr
  dsimp only
  rw [kernel,if_pos hr,gain_smooth_eq
    ⟨hgeo.1,hgeo.2.1⟩ ⟨hgeo.1.trans hgeo.2.2.1,hgeo.2.2.2⟩]
  exact (div_eq_mul_one_div _ _).symm

theorem five_original66 {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ v : ℝ × ℝ, FullFive.kernel p H v) = WuPaper.R2Xi.original66 H p := by
  change (∫ v : ℝ × ℝ, kernel p .gammaFive H v) = _
  rw [literal_integral hp .gammaFive hm hb]
  unfold WuPaper.R2Xi.original66
  apply intervalIntegral.integral_congr
  intro t ht
  have ho : 1 / p.S ≤ 1 / p.kappa2 := (gain_endpoint_order hp .gammaFive).2.1
  have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa2) := by
    simpa only [upperP,uIcc_of_le ho] using ht
  dsimp only [upperQ,lowerQ,Hratio]
  rw [max_eq_right ht'.1,min_eq_right ht'.2,← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have he : p.S * (1 - t - u) = p.S - p.S * t - p.S * u := by ring
  rw [he]
  simp only [div_eq_mul_inv,mul_inv]
  ring

theorem other_kernel_eq {p : SecondFunctionalParameters} (hp : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) (H : ℝ → ℝ) :
    ProfileGrid.kernel p j H = kernel p j H := by
  funext v
  unfold ProfileGrid.kernel kernel
  rw [fullH_gainRegion_eq hp j hj]
  rfl

end Wu18938Campaign.M1.Confirmed.PairLiteral
