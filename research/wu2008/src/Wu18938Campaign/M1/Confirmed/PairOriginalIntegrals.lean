import Wu18938Campaign.M1.Confirmed.PairLiteralKernel

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.PairLiteral

open Wu2008DoubleSieve MotherPair Set Real MeasureTheory Filter
open scoped Classical Interval

theorem inner_eq {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (1 / p.S) (upperP p j)) :
    (∫ u, kernel p j H (t,u)) =
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        H (Hratio p j t u) / (t * u * (1 - t - u)) := by
  have hs : Function.support (fun u => kernel p j H (t,u)) ⊆
      Icc (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
    intro u hu
    have hr : PairRegion p j t u := by
      by_contra hn
      exact hu (if_neg hn)
    exact (pairRegion_iff_slice hp j ht u).mp hr
  rw [truncatedSixthMass_integral_eq_interval (min_le_left _ _) hs]
  apply intervalIntegral.integral_congr
  intro u hu
  have hr := (pairRegion_iff_slice hp j ht u).mpr
    (by simpa only [uIcc_of_le (gain_start_bounds hp j ht).2.2] using hu)
  have hg := pairRegion_bounds hp j hr
  dsimp only
  rw [kernel,if_pos hr,gain_smooth_eq ⟨hg.1,hg.2.1⟩ ⟨hg.1.trans hg.2.2.1,hg.2.2.2⟩]
  exact (div_eq_mul_one_div _ _).symm

theorem outer_integrable {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    IntervalIntegrable (fun t =>
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        H (Hratio p j t u) / (t * u * (1 - t - u))) volume (1 / p.S) (upperP p j) := by
  apply (kernel_integrable hp j hm hb).integral_prod_left.intervalIntegrable.congr
  intro t ht
  exact inner_eq hp j H
    (by simpa only [uIcc_of_le (gain_endpoint_order hp j).2.1] using uIoc_subset_uIcc ht)

theorem six_original67 {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ v : ℝ × ℝ, kernel p .gammaSix H v) = WuPaper.R2Xi.original67 H p := by
  rw [literal_integral hp .gammaSix hm hb]
  unfold WuPaper.R2Xi.original67
  apply intervalIntegral.integral_congr
  intro t ht
  have ho := parameter_order hp
  have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa1) := by
    simpa only [upperP,uIcc_of_le ho.2.1] using ht
  dsimp only [upperQ,lowerQ,Hratio]
  rw [max_eq_left (ht'.2.trans ho.2.2.1.le),min_eq_right ho.2.2.2.1.le,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show p.S * (1 - t - u) = p.S - p.S * t - p.S * u by ring]
  simp only [div_eq_mul_inv,mul_inv]
  ring

theorem selected_integrable {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (1 / p.S) (1 / p.kappa1)) :
    IntervalIntegrable (fun u => H ((1 - t - u) / t) / (t * u * (1 - t - u)))
      volume t (1 / p.kappa2) := by
  have ho := parameter_order hp
  have htk : t ≤ 1 / p.kappa2 := ht.2.trans ho.2.2.1.le
  have hi : IntegrableOn (fun u => H ((1 - t - u) / t) * gainSmooth p (t,u))
      (Icc t (1 / p.kappa2)) := by
    apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      (((hm.comp (by fun_prop)).mul
        ((gain_smooth_continuous hp).measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    apply Eventually.of_forall
    intro u
    change ‖H ((1 - t - u) / t) * gainSmooth p (t,u)‖ ≤ 25 / (1 - 2 * (1 / p.kappa3))
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gain_smooth_bounds hp (t,u)).1]
    exact (mul_le_mul_of_nonneg_right (hb _) (gain_smooth_bounds hp (t,u)).1).trans
      (by simpa only [one_mul] using (gain_smooth_bounds hp (t,u)).2)
  apply ((intervalIntegrable_iff_integrableOn_Icc_of_le htk).mpr hi).congr
  intro u hu
  have hu' : u ∈ Icc t (1 / p.kappa2) := by
    simpa only [uIcc_of_le htk] using uIoc_subset_uIcc hu
  dsimp only
  rw [gain_smooth_eq
    ⟨ht.1,htk.trans ho.2.2.2.1.le⟩
    ⟨ht.1.trans hu'.1,hu'.2.trans ho.2.2.2.1.le⟩]
  exact (div_eq_mul_one_div _ _).symm

theorem seven_eight_original68 {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ v : ℝ × ℝ, kernel p .gammaSeven H v) +
      (∫ v : ℝ × ℝ, kernel p .gammaEight H v) = WuPaper.R2Xi.original68 H p := by
  rw [literal_integral hp .gammaSeven hm hb,literal_integral hp .gammaEight hm hb]
  have hi7 := outer_integrable hp .gammaSeven hm hb
  have hi8 := outer_integrable hp .gammaEight hm hb
  simp only [upperP] at hi7 hi8 ⊢
  rw [← intervalIntegral.integral_add hi7 hi8]
  unfold WuPaper.R2Xi.original68
  apply intervalIntegral.integral_congr
  intro t ht
  have ho := parameter_order hp
  have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa1) := by
    simpa only [upperP,uIcc_of_le ho.2.1] using ht
  dsimp only [upperQ,lowerQ,Hratio]
  rw [max_eq_right ht'.1,min_eq_right ht'.2,
    max_eq_left ht'.2,min_eq_right ho.2.2.1.le,← intervalIntegral.integral_div]
  have hi := selected_integrable hp hm hb ht'
  have hi1 := hi.mono_set (by
    rw [uIcc_of_le ht'.2,uIcc_of_le (ht'.2.trans ho.2.2.1.le)]
    exact Icc_subset_Icc le_rfl ho.2.2.1.le)
  have hi2 := hi.mono_set (by
    rw [uIcc_of_le ho.2.2.1.le,uIcc_of_le (ht'.2.trans ho.2.2.1.le)]
    exact Icc_subset_Icc ht'.2 le_rfl)
  rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  simp only [div_eq_mul_inv,mul_inv]
  ring

theorem four_original_integrals {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∑ k : Term, ∫ v : ℝ × ℝ, kernel p k H v) =
      WuPaper.R2Xi.original66 H p + WuPaper.R2Xi.original67 H p + WuPaper.R2Xi.original68 H p := by
  rw [show (Finset.univ : Finset Term) =
      {Term.gammaFive,Term.gammaSix,Term.gammaSeven,Term.gammaEight} by ext k; cases k <;> simp]
  simp only [Finset.sum_insert (by decide : Term.gammaFive ∉
      {Term.gammaSix,Term.gammaSeven,Term.gammaEight}),
    Finset.sum_insert (by decide : Term.gammaSix ∉ {Term.gammaSeven,Term.gammaEight}),
    Finset.sum_insert (by decide : Term.gammaSeven ∉ {Term.gammaEight}),Finset.sum_singleton]
  rw [show (∫ v : ℝ × ℝ, kernel p .gammaFive H v) = WuPaper.R2Xi.original66 H p from
    five_original66 hp hm hb,six_original67 hp hm hb,seven_eight_original68 hp hm hb]
  ring

end Wu18938Campaign.M1.Confirmed.PairLiteral
