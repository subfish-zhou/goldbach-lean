import MathlibNt.Wu2008DoubleSieve.MotherPairGainIntegral

namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem classicalIntegral_literal (p : SecondFunctionalParameters) (j : Term) :
    classicalIntegral p j = ∫ t in (1/p.S)..(upperP p j),
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        1/(t*u*(1-t-u)) := by
  cases j <;> rfl

theorem classical_inner_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) :
    IntervalIntegrable (fun u => 1/(t*u*(1-t-u))) volume
      (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
  have hc : ContinuousOn (fun u => 1/(t*u*(1-t-u)))
      (uIcc (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j)) := by
    apply continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).mul
        ((continuousOn_const.sub continuousOn_const).sub continuousOn_id))
    intro u hu
    apply ne_of_gt (pair_denominator_bound h j ?_).1
    apply (pairRegion_iff_slice h j ht u).mpr
    simpa only [uIcc_of_le (gain_start_bounds h j ht).2.2] using hu
  exact hc.intervalIntegrable

theorem classical_inner_eq_section {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) :
    (∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j), 1/(t*u*(1-t-u))) =
    kernelSection (1/p.kappa3) (lowerQ p j) (upperQ p j) t / t := by
  unfold kernelSection
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
    simpa only [gamma5MassSectionStart,uIcc_of_le (gain_start_bounds h j ht).2.2] using hu
  have hr := pairRegion_bounds h j ((pairRegion_iff_slice h j ht u).mpr hu')
  dsimp only
  rw [clipH_eq hr.2.1 hr.2.2.2]
  simp only [div_eq_mul_inv,mul_inv]
  ring

theorem classical_outer_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : IntervalIntegrable
    (fun t => ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
      1/(t*u*(1-t-u))) volume (1/p.S) (upperP p j) := by
  obtain ⟨ha,hAB,hBU,hAC,hCD,hDU,hU⟩ := gain_endpoint_order h j
  have hA : (1/10:ℝ) ≤ 1/p.S := by linarith
  have hc := primeOrdered_continuous_of_lipschitz
    (fun x _ y _ => (kernelSection_regular hU (hA.trans hAC) hCD (hDU.trans hU.le)).2 x y)
  apply (primeOrdered_integrable hc ⟨hA,(hAB.trans hBU).trans hU.le⟩
    ⟨hA.trans hAB,hBU.trans hU.le⟩).congr
  intro t ht
  exact (classical_inner_eq_section h j
    (by simpa only [uIcc_of_le hAB] using uIoc_subset_uIcc ht)).symm

theorem gain_literal_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ t u : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hv : PairRegion p j t u) :
    0 ≤ gainLiteral p j δ t u ∧ gainLiteral p j δ t u ≤ 1/(t*u*(1-t-u)) := by
  have hd := (pair_denominator_bound h j hv).1
  by_cases hl : gamma5GainLegal t u
  · have hh := gamma5Gain_H_bounds hδ hδhi (Hratio p j t u)
    rw [gain_clip_eq h j ⟨hv,hl⟩] at hh
    simp only [gainLiteral,hl,if_true]
    exact ⟨div_nonneg hh.1 hd.le,div_le_div_of_nonneg_right hh.2 hd.le⟩
  · simp only [gainLiteral,hl,if_false]
    exact ⟨le_rfl,by positivity⟩

theorem gainIntegral_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    0 ≤ gainIntegral p j δ ∧ gainIntegral p j δ ≤ classicalIntegral p j := by
  constructor
  · rw [gain_integral_eq h j hδ hδhi]
    exact integral_nonneg (fun v => (gain_kernel_bounds h j hδ hδhi v).1)
  · rw [classicalIntegral_literal]
    apply intervalIntegral.integral_mono_on (gain_endpoint_order h j).2.1
      (gain_outer_integrable h j hδ hδhi) (classical_outer_integrable h j)
    intro t ht
    apply intervalIntegral.integral_mono_on (gain_start_bounds h j ht).2.2
      (gain_inner_integrable h j hδ hδhi ht) (classical_inner_integrable h j ht)
    intro u hu
    exact (gain_literal_bounds h j hδ hδhi ((pairRegion_iff_slice h j ht u).mpr hu)).2

theorem fullH_pair_legal {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) {t u : ℝ} (hv : PairRegion p j t u) :
    gamma5GainLegal t u := by
  obtain ⟨ht,htb,htu,hue⟩ := fullH_region_bounds h j hj hv
  have hd := fullH_domain h ht htb htu hue
  exact ⟨hd.2.2.1.le,hd.2.2.2.1.le⟩

theorem fullH_gainRegion_eq {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) :
    gainRegion p j = {v : ℝ × ℝ | PairRegion p j v.1 v.2} := by
  ext v
  exact ⟨fun hv => hv.1,fun hv => ⟨hv,fullH_pair_legal h j hj hv⟩⟩

theorem fullH_gain_literal_eq {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) {δ t u : ℝ} (hv : PairRegion p j t u) :
    gainLiteral p j δ t u = wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u)) := by
  simp only [gainLiteral,fullH_pair_legal h j hj hv,if_true]

theorem fullH_gainIntegral_uncut {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) (δ : ℝ) :
    gainIntegral p j δ = ∫ t in (1/p.S)..(upperP p j),
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u)) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1/p.S) (upperP p j) := by
    simpa only [uIcc_of_le (gain_endpoint_order h.toAnalyticParameters j).2.1] using ht
  apply intervalIntegral.integral_congr
  intro u hu
  apply fullH_gain_literal_eq h j hj
  apply (pairRegion_iff_slice h.toAnalyticParameters j ht' u).mpr
  simpa only [uIcc_of_le (gain_start_bounds h.toAnalyticParameters j ht').2.2] using hu

theorem fullH_gammaSix_integral {p : SecondFunctionalParameters} (h : FullHParameters p) (δ : ℝ) :
    gainIntegral p .gammaSix δ = ∫ t in (1/p.S)..(1/p.kappa1),
      ∫ u in (1/p.kappa2)..(1/p.kappa3),
        wuImprovementLimit true δ (p.S*(1-t-u))/(t*u*(1-t-u)) := by
  rw [fullH_gainIntegral_uncut h .gammaSix (by intro he; cases he)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1/p.S) (1/p.kappa1) := by
    simpa only [upperP,uIcc_of_le (parameter_order h.toAnalyticParameters).2.1] using ht
  obtain ⟨_,_,hbc,hce,_,_⟩ := parameter_order h.toAnalyticParameters
  simp only [upperQ,lowerQ,Hratio,max_eq_left (ht'.2.trans hbc.le),min_eq_right hce.le]

theorem fullH_gammaSeven_integral {p : SecondFunctionalParameters} (h : FullHParameters p) (δ : ℝ) :
    gainIntegral p .gammaSeven δ = ∫ t in (1/p.S)..(1/p.kappa1), ∫ u in t..(1/p.kappa1),
      wuImprovementLimit true δ ((1-t-u)/t)/(t*u*(1-t-u)) := by
  rw [fullH_gainIntegral_uncut h .gammaSeven (by intro he; cases he)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1/p.S) (1/p.kappa1) := by
    simpa only [upperP,uIcc_of_le (parameter_order h.toAnalyticParameters).2.1] using ht
  simp only [upperQ,lowerQ,Hratio,max_eq_right ht'.1,min_eq_right ht'.2]

theorem fullH_gammaEight_integral {p : SecondFunctionalParameters} (h : FullHParameters p) (δ : ℝ) :
    gainIntegral p .gammaEight δ = ∫ t in (1/p.S)..(1/p.kappa1), ∫ u in (1/p.kappa1)..(1/p.kappa2),
      wuImprovementLimit true δ ((1-t-u)/t)/(t*u*(1-t-u)) := by
  rw [fullH_gainIntegral_uncut h .gammaEight (by intro he; cases he)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1/p.S) (1/p.kappa1) := by
    simpa only [upperP,uIcc_of_le (parameter_order h.toAnalyticParameters).2.1] using ht
  simp only [upperQ,lowerQ,Hratio,max_eq_left ht'.2,
    min_eq_right (parameter_order h.toAnalyticParameters).2.2.1.le]

/-- This is an interval-integral statement only, not a finite prime-atom assertion. -/
theorem gainIntegral_collapsed {p : SecondFunctionalParameters} (he : p.S = p.kappa1)
    (j : Term) (hj : j ≠ .gammaFive) (δ : ℝ) : gainIntegral p j δ = 0 := by
  cases j with
  | gammaFive => exact False.elim (hj rfl)
  | gammaSix => simp only [gainIntegral,upperP,he,intervalIntegral.integral_same]
  | gammaSeven => simp only [gainIntegral,upperP,he,intervalIntegral.integral_same]
  | gammaEight => simp only [gainIntegral,upperP,he,intervalIntegral.integral_same]

end Wu2008DoubleSieve.MotherPair
