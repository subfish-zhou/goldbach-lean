import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132ExactParityTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The positive amount removed when the plus hat tail at its closed threshold
is rewritten with the shifted weight `t - 1`. -/
noncomputable def lemma132HatTailSlack (H : Section13HatLayers) : ℝ :=
  ∫ t in Ioi (3 : ℝ), H.T .minus (t - 1)

/-- The Section 13 plus-tail identity remains valid at the closed threshold
`a = 3`.  The published open-tail lemma cannot be applied directly there, so
we apply the same improper-FTC theorem using continuity at `3` and the DDE on
`(3,∞)`. -/
theorem integral_Ioi_hatTailIntegrand_plus_three
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    IntegrableOn (hatTailIntegrand H .plus) (Ioi (3 : ℝ)) ∧
      (∫ t in Ioi (3 : ℝ), hatTailIntegrand H .plus t) =
        weightedHat H .plus 3 := by
  let f : ℝ → ℝ := weightedHat H .plus
  let f' : ℝ → ℝ := fun t => -hatTailIntegrand H .plus t
  have hTcont : ContinuousAt (H.T .plus) 3 :=
    (hH.continuous .plus).continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
  have hcont : ContinuousWithinAt f (Ici (3 : ℝ)) 3 := by
    exact ((continuousAt_id.pow 2).mul hTcont).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (3 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    simpa [f, f', hatTailIntegrand, neg_mul] using
      hH.dde .plus x (by
        have hx' : 3 < x := hx
        norm_num [ErrorSign.epsilon]
        exact hx')
  have hnonpos : ∀ x ∈ Ioi (3 : ℝ), f' x ≤ 0 := by
    intro x hx
    have hx' : 3 < x := hx
    dsimp only [f', hatTailIntegrand]
    exact neg_nonpos.mpr (mul_nonneg (by linarith [hx'] : 0 ≤ x)
      (hH.positive .minus (x - 1) (by linarith [hx'])).le)
  have hi : IntegrableOn f' (Ioi (3 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv hnonpos
      (by simpa only [f] using hH.weighted_tendsto_zero .plus)
  have htail : IntegrableOn (hatTailIntegrand H .plus) (Ioi (3 : ℝ)) := by
    have hineg := hi.neg
    change IntegrableOn (fun t => -f' t) (Ioi (3 : ℝ)) at hineg
    exact hineg.congr (ae_of_all _ fun t => by simp [f', hatTailIntegrand])
  refine ⟨htail, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hnonpos
    (by simpa only [f] using hH.weighted_tendsto_zero .plus)
  simpa only [f', MeasureTheory.integral_neg, zero_sub, neg_inj] using h

/-- The unweighted delayed minus tail defining `lemma132HatTailSlack` is finite. -/
theorem integrableOn_lemma132HatTailSlack
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    IntegrableOn (fun t => H.T .minus (t - 1)) (Ioi (3 : ℝ)) := by
  have htail := (integral_Ioi_hatTailIntegrand_plus_three hH).1
  apply htail.mono'
  · apply ContinuousOn.aestronglyMeasurable
    · apply (hH.continuous .minus).comp
        (continuousOn_id.sub continuousOn_const)
      intro t ht
      have ht' : 3 < t := ht
      change 0 < t - 1
      linarith [ht']
    · exact measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 3 < t := ht
    have hpos : 0 < H.T .minus (t - 1) :=
      hH.positive .minus (t - 1) (by linarith [ht'])
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    dsimp only [hatTailIntegrand, ErrorSign.opposite]
    nlinarith [ht']

/-- The endpoint slack is strictly positive. -/
theorem lemma132HatTailSlack_pos
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    0 < lemma132HatTailSlack H := by
  let u : ℝ → ℝ := fun t => H.T .minus (t - 1)
  have hu := integrableOn_lemma132HatTailSlack hH
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (3 : ℝ))] u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 3 < t := ht
    exact (hH.positive .minus (t - 1) (by linarith [ht'])).le
  rw [lemma132HatTailSlack]
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg hu).2
  have hsubset : Ioc (3 : ℝ) 4 ⊆ Function.support u := by
    intro t ht
    exact ne_of_gt (hH.positive .minus (t - 1) (by linarith [ht.1]))
  calc
    0 < (volume.restrict (Ioi (3 : ℝ))) (Ioc 3 4) := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      simp only [Ioc_inter_Ioi, max_eq_left (by norm_num : (3 : ℝ) ≤ 3)]
      rw [Real.volume_Ioc]
      norm_num
    _ ≤ (volume.restrict (Ioi (3 : ℝ))) (Function.support u) :=
      measure_mono hsubset

/-- Closed-threshold decomposition: the shifted weighted tail is exactly the
normalized plus hat value minus the strictly positive slack. -/
theorem lemma132_weightedHat_plus_three_endpoint_slack
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    IntegrableOn (fun t => (t - 1) * H.T .minus (t - 1)) (Ioi (3 : ℝ)) ∧
      (∫ t in Ioi (3 : ℝ), (t - 1) * H.T .minus (t - 1)) =
        weightedHat H .plus 3 - lemma132HatTailSlack H ∧
      weightedHat H .plus 3 - lemma132HatTailSlack H =
        1 - lemma132HatTailSlack H := by
  let u : ℝ → ℝ := fun t => H.T .minus (t - 1)
  let v : ℝ → ℝ := fun t => (t - 1) * H.T .minus (t - 1)
  have htail := integral_Ioi_hatTailIntegrand_plus_three hH
  have hu : IntegrableOn u (Ioi (3 : ℝ)) := integrableOn_lemma132HatTailSlack hH
  have hv : IntegrableOn v (Ioi (3 : ℝ)) := by
    have hd := htail.1.sub hu
    exact hd.congr (ae_of_all _ fun t => by
      dsimp [v, u, hatTailIntegrand]
      ring)
  refine ⟨hv, ?_, ?_⟩
  · have hadd := MeasureTheory.integral_add hv hu
    have hpoint : (fun t => v t + u t) = hatTailIntegrand H .plus := by
      funext t
      dsimp [v, u, hatTailIntegrand]
      ring
    rw [hpoint] at hadd
    rw [lemma132HatTailSlack]
    dsimp only [v, u] at hadd ⊢
    linarith [htail.2]
  · have hinit := hH.initial_plus 3 (by norm_num) (by norm_num)
    have hval : weightedHat H .plus 3 = 1 := by
      norm_num at hinit ⊢
      exact hinit
    rw [hval]


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
