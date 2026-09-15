import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceIntegralDDE

/-!
# Final source-pairing closure for Suzuki Proposition 11.8

The genuine source pairing is continuous on every `[2,M]` and has zero right
 derivative at every point of `[2,M)`, including the lower endpoint `2` and the
 kink `3`.  The right-derivative constant theorem therefore proves conservation
 on the whole closed interval in one step.  Decay at infinity then forces the
 boundary scalar, and hence Suzuki's `B`, to vanish.
-/

open scoped Classical BigOperators Interval ENNReal
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

private noncomputable def sourceWeighted (s : ℝ) : ℝ :=
  s * suzukiProposition118SourceQ s

private noncomputable def sourceWeightedPrimitive (s : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..s, sourceWeighted t

/-- The source is right-continuous at every point of its closed history/series
range `[1,∞)`.  At `2` this is genuinely one-sided and follows from continuity
of the weighted source on the series side. -/
private theorem continuousWithinAt_sourceQ_Ici
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 1 ≤ s) :
    ContinuousWithinAt suzukiProposition118SourceQ (Ici s) s := by
  by_cases hs2 : s < 2
  · have hs0 : s ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hs)
    have hrat : ContinuousAt
        (fun u : ℝ => SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude / u) s :=
      continuousAt_const.div continuousAt_id hs0
    apply hrat.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hs2)] with u hu
      rw [suzukiProposition118SourceQ, if_pos hu]
    · rw [suzukiProposition118SourceQ, if_pos hs2]
  · have hs2' : 2 ≤ s := le_of_not_gt hs2
    have hW := continuousOn_weighted_suzukiProposition118SourceQ hH
      (M := s + 1) (by linarith)
    have hWsmall : ContinuousWithinAt sourceWeighted (Icc s (s + 1)) s := by
      apply (hW.continuousWithinAt ⟨hs2', by linarith⟩).mono
      intro u hu
      exact ⟨hs2'.trans hu.1, hu.2⟩
    have hsets : Icc s (s + 1) =ᶠ[𝓝 s] Ici s := by
      filter_upwards [Iio_mem_nhds (by linarith : s < s + 1)] with u hu
      apply propext
      change (s ≤ u ∧ u ≤ s + 1) ↔ s ≤ u
      exact ⟨fun h => h.1, fun h => ⟨h, hu.le⟩⟩
    have hWright : ContinuousWithinAt sourceWeighted (Ici s) s :=
      hWsmall.congr_set hsets
    have hdiv := hWright.div continuousWithinAt_id (ne_of_gt (by linarith : 0 < s))
    apply hdiv.congr
    · intro u hu
      change s ≤ u at hu
      dsimp [sourceWeighted]
      field_simp [ne_of_gt (by linarith [hu] : 0 < u)]
    · dsimp [sourceWeighted]
      field_simp [ne_of_gt (by linarith : 0 < s)]

private theorem continuousWithinAt_sourceWeighted_Ici
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 1 ≤ s) :
    ContinuousWithinAt sourceWeighted (Ici s) s := by
  exact continuousWithinAt_id.mul (continuousWithinAt_sourceQ_Ici hH hs)

private theorem sourceWeighted_intervalIntegrable_history
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    IntervalIntegrable sourceWeighted volume x y := by
  have hc : IntervalIntegrable
      (fun _ : ℝ => SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude)
      volume x y := continuousOn_const.intervalIntegrable
  apply hc.congr_ae
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (μ := volume) (2 : ℝ))
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_uIoc] with t ht2 ht
  rw [uIoc_of_le hxy] at ht
  have htlt : t < 2 := lt_of_le_of_ne (ht.2.trans hy) (fun h => ht2 h)
  dsimp [sourceWeighted]
  rw [suzukiProposition118SourceQ, if_pos htlt]
  have ht0 : t ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hx.trans ht.1.le))
  field_simp [ht0]

/-- The weighted source is locally interval-integrable from the closed history
endpoint `1`.  The only possible jump, at `2`, is harmless. -/
private theorem sourceWeighted_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable sourceWeighted volume x y := by
  by_cases hy : y ≤ 2
  · exact sourceWeighted_intervalIntegrable_history hx hxy hy
  · have h2y : 2 ≤ y := le_of_not_ge hy
    by_cases hx2 : 2 ≤ x
    · have hc : ContinuousOn sourceWeighted (Set.uIcc x y) := by
        rw [uIcc_of_le hxy]
        change ContinuousOn (fun s => s * suzukiProposition118SourceQ s) (Icc x y)
        exact (continuousOn_weighted_suzukiProposition118SourceQ hH h2y).mono
          (by intro s hs; exact ⟨hx2.trans hs.1, hs.2⟩)
      exact hc.intervalIntegrable
    · have hxle2 : x ≤ 2 := le_of_not_ge hx2
      have hlo := sourceWeighted_intervalIntegrable_history hx hxle2 le_rfl
      have hhi : IntervalIntegrable sourceWeighted volume 2 y := by
        have hc : ContinuousOn sourceWeighted (Set.uIcc (2 : ℝ) y) := by
          rw [uIcc_of_le h2y]
          change ContinuousOn (fun s => s * suzukiProposition118SourceQ s) (Icc 2 y)
          exact continuousOn_weighted_suzukiProposition118SourceQ hH h2y
        exact hc.intervalIntegrable
      exact hlo.trans hhi

private theorem stronglyMeasurableAtFilter_sourceWeighted_Ioi
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 1 ≤ s) :
    StronglyMeasurableAtFilter sourceWeighted (𝓝[Ioi s] s) volume := by
  refine ⟨Ioc s (s + 1), ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio (s + 1), Iio_mem_nhds (by linarith), ?_⟩
    intro u hu
    exact ⟨hu.2, hu.1.le⟩
  · exact (((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : s ≤ s + 1)).1
      (sourceWeighted_intervalIntegrable hH hs (by linarith))).mono_set
        Ioc_subset_Icc_self).aestronglyMeasurable

/-- Right FTC for the locally integrable weighted source primitive. -/
private theorem hasDerivWithinAt_sourceWeightedPrimitive_right
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 1 ≤ s) :
    HasDerivWithinAt sourceWeightedPrimitive (sourceWeighted s) (Ici s) s := by
  have h := intervalIntegral.integral_hasDerivWithinAt_right
    (sourceWeighted_intervalIntegrable hH (x := (1 : ℝ)) (y := s) (by norm_num) hs)
    (s := Ici s) (t := Ioi s)
    (stronglyMeasurableAtFilter_sourceWeighted_Ioi hH hs)
    ((continuousWithinAt_sourceWeighted_Ici hH hs).mono Ioi_subset_Ici_self)
  change HasDerivWithinAt (fun u => ∫ t in (1 : ℝ)..u, sourceWeighted t)
    (sourceWeighted s) (Ici s) s
  exact h

/-- The integral DDE differentiates from the right at every `s ≥ 2`, including
`s=2` and the kink `s=3`. -/
private theorem hasDerivWithinAt_sourceWeighted_right
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    HasDerivWithinAt sourceWeighted
      (-suzukiProposition118SourceQ (s - 1)) (Ici s) s := by
  let f : ℝ → ℝ := fun t => suzukiProposition118SourceQ (t - 1)
  have hfcont : ContinuousWithinAt f (Ici s) s := by
    have hshift : ContinuousWithinAt (fun u : ℝ => u - 1) (Ici s) s :=
      ((hasDerivAt_id s).sub_const 1).continuousAt.continuousWithinAt
    have hc := ContinuousWithinAt.comp
      (f := fun u : ℝ => u - 1) (g := suzukiProposition118SourceQ)
      (s := Ici s) (t := Ici (s - 1))
      (continuousWithinAt_sourceQ_Ici hH (s := s - 1) (by linarith)) hshift
      (by
        intro u hu
        change s ≤ u at hu
        change s - 1 ≤ u - 1
        exact sub_le_sub_right hu 1)
    exact hc
  have hfmeas : StronglyMeasurableAtFilter f (𝓝[Ioi s] s) volume := by
    refine ⟨Ioc s (s + 1), ?_, ?_⟩
    · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Iio (s + 1), Iio_mem_nhds (by linarith), ?_⟩
      intro u hu
      exact ⟨hu.2, hu.1.le⟩
    · exact (((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : s ≤ s + 1)).1
        (suzukiProposition118SourceQ_shift_intervalIntegrable hH hs (by linarith))).mono_set
          Ioc_subset_Icc_self).aestronglyMeasurable
  have hprim := intervalIntegral.integral_hasDerivWithinAt_right
    (suzukiProposition118SourceQ_shift_intervalIntegrable hH
      (x := (2 : ℝ)) (y := s) (by norm_num) hs)
    (s := Ici s) (t := Ioi s) hfmeas (hfcont.mono Ioi_subset_Ici_self)
  have hbase := hprim.neg.const_add
    ((2 : ℝ) * suzukiProposition118SourceQ 2)
  apply hbase.congr
  · intro u hu
    have hdde := suzukiProposition118SourceQ_weighted_sub hH
      (x := (2 : ℝ)) (y := u) (by norm_num) (hs.trans hu)
    dsimp [sourceWeighted, f]
    linarith
  · have hdde := suzukiProposition118SourceQ_weighted_sub hH
      (x := (2 : ℝ)) (y := s) (by norm_num) hs
    dsimp [sourceWeighted, f]
    linarith

/-- The moving unit-window integral of `tQ(t)` has the expected right
derivative, with no smoothness assumption across `t=2`. -/
private theorem hasDerivWithinAt_sourceWeighted_movingWindow_right
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    HasDerivWithinAt
      (fun u => ∫ t in u - 1..u, sourceWeighted t)
      (sourceWeighted s - sourceWeighted (s - 1)) (Ici s) s := by
  have hright := hasDerivWithinAt_sourceWeightedPrimitive_right hH (s := s) (by linarith)
  have hleft0 := hasDerivWithinAt_sourceWeightedPrimitive_right hH
    (s := s - 1) (by linarith)
  have hshift : HasDerivWithinAt (fun u : ℝ => u - 1) 1 (Ici s) s :=
    ((hasDerivAt_id s).sub_const 1).hasDerivWithinAt
  have hmap : MapsTo (fun u : ℝ => u - 1) (Ici s) (Ici (s - 1)) := by
    intro u hu
    change s ≤ u at hu
    exact sub_le_sub_right hu 1
  have hleft := hleft0.comp s hshift hmap
  have hsub0 := hright.sub hleft
  have hsub : HasDerivWithinAt
      (sourceWeightedPrimitive - sourceWeightedPrimitive ∘ fun u => u - 1)
      (sourceWeighted s - sourceWeighted (s - 1)) (Ici s) s :=
    hsub0.congr_deriv (by rw [mul_one])
  apply hsub.congr
  · intro u hu
    have hu1 : 1 ≤ u - 1 := by linarith [hs.trans hu]
    have huu : u - 1 ≤ u := by linarith
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (sourceWeighted_intervalIntegrable hH (x := (1 : ℝ)) (y := u - 1)
        (by norm_num) hu1)
      (sourceWeighted_intervalIntegrable hH (x := u - 1) (y := u) hu1 huu)
    dsimp [sourceWeightedPrimitive] at hadd ⊢
    linarith
  · have hu1 : 1 ≤ s - 1 := by linarith
    have huu : s - 1 ≤ s := by linarith
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (sourceWeighted_intervalIntegrable hH (x := (1 : ℝ)) (y := s - 1)
        (by norm_num) hu1)
      (sourceWeighted_intervalIntegrable hH (x := s - 1) (y := s) hu1 huu)
    dsimp [sourceWeightedPrimitive] at hadd ⊢
    linarith

/-- The genuine source pairing has zero right derivative throughout `[2,∞)`,
including both exceptional endpoints required by the one-sided argument. -/
theorem hasDerivWithinAt_suzukiProposition118SourceQPairing_right
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    HasDerivWithinAt suzukiProposition118SourceQPairing 0 (Ici s) s := by
  have hq : HasDerivWithinAt (fun u : ℝ => u - 1) 1 (Ici s) s :=
    ((hasDerivAt_id s).sub_const 1).hasDerivWithinAt
  have hW := hasDerivWithinAt_sourceWeighted_right hH hs
  have hpoint := hq.mul hW
  have hwindow := hasDerivWithinAt_sourceWeighted_movingWindow_right hH hs
  have hout0 := hpoint.sub hwindow
  have hout : HasDerivWithinAt
      ((fun u : ℝ => u - 1) * sourceWeighted -
        fun u => ∫ t in u - 1..u, sourceWeighted t)
      0 (Ici s) s :=
    hout0.congr_deriv (by dsimp [sourceWeighted]; ring)
  apply hout.congr_of_eventuallyEq
  · filter_upwards [] with u
    simp only [suzukiProposition118SourceQPairing, section10SignedPairing, one_mul]
    dsimp [sourceWeighted]
    congr 1
    · ring
    · apply intervalIntegral.integral_congr
      intro t _
      ring
  · simp only [suzukiProposition118SourceQPairing, section10SignedPairing, one_mul]
    dsimp [sourceWeighted]
    congr 1
    · ring
    · apply intervalIntegral.integral_congr
      intro t _
      ring

/-- Continuity of the source pairing on every compact interval of its legal
range. -/
theorem continuousOn_suzukiProposition118SourceQPairing
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {M : ℝ} (hM : 2 ≤ M) :
    ContinuousOn suzukiProposition118SourceQPairing (Icc 2 M) := by
  have hW := continuousOn_weighted_suzukiProposition118SourceQ hH hM
  have hInt := sourceWeighted_intervalIntegrable hH
    (x := (1 : ℝ)) (y := M) (by norm_num) (by linarith)
  have hIntOn : IntegrableOn sourceWeighted (Icc 1 M) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (1 : ℝ) ≤ M)).1 hInt
  have hJset := intervalIntegral.continuousOn_primitive hIntOn
  have hJ : ContinuousOn sourceWeightedPrimitive (Icc 1 M) := by
    apply hJset.congr
    intro s hs
    change (∫ t in (1 : ℝ)..s, sourceWeighted t) =
      ∫ t in Ioc (1 : ℝ) s, sourceWeighted t
    exact intervalIntegral.integral_of_le hs.1
  have hJright : ContinuousOn (fun s => sourceWeightedPrimitive s) (Icc 2 M) :=
    hJ.mono (Icc_subset_Icc_left (by norm_num : (1 : ℝ) ≤ 2))
  have hJleft : ContinuousOn (fun s => sourceWeightedPrimitive (s - 1)) (Icc 2 M) := by
    apply hJ.comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change 1 ≤ s - 1 ∧ s - 1 ≤ M
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmodel : ContinuousOn
      (fun s => (s - 1) * sourceWeighted s -
        (sourceWeightedPrimitive s - sourceWeightedPrimitive (s - 1)))
      (Icc 2 M) := by
    exact ((continuousOn_id.sub continuousOn_const).mul hW).sub (hJright.sub hJleft)
  apply hmodel.congr
  intro s hs
  have hs1 : 1 ≤ s - 1 := by linarith [hs.1]
  have hss : s - 1 ≤ s := by linarith
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (sourceWeighted_intervalIntegrable hH (x := (1 : ℝ)) (y := s - 1)
      (by norm_num) hs1)
    (sourceWeighted_intervalIntegrable hH (x := s - 1) (y := s) hs1 hss)
  simp only [suzukiProposition118SourceQPairing, section10SignedPairing, one_mul,
    suzukiProposition118KappaOneSourceAdjoint]
  dsimp [sourceWeighted, sourceWeightedPrimitive] at hadd ⊢
  simp only [add_sub_cancel_right]
  linarith

/-- Conservation of the genuine source pairing on all of `[2,∞)`. -/
theorem suzukiProposition118SourceQPairing_eq_lowerBoundary
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {y : ℝ} (hy : 2 ≤ y) :
    suzukiProposition118SourceQPairing y =
      suzukiProposition118SourceQPairing 2 := by
  exact constant_of_has_deriv_right_zero
    (continuousOn_suzukiProposition118SourceQPairing hH hy)
    (fun x hx => hasDerivWithinAt_suzukiProposition118SourceQPairing_right hH hx.1)
    y ⟨hy, le_rfl⟩

/-- The genuine source pairing vanishes at every legal coordinate. -/
theorem suzukiProposition118SourceQPairing_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {y : ℝ} (hy : 2 ≤ y) :
    suzukiProposition118SourceQPairing y = 0 := by
  have hev : suzukiProposition118SourceQPairing =ᶠ[atTop]
      (fun _ => suzukiProposition118SourceQPairing 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    exact suzukiProposition118SourceQPairing_eq_lowerBoundary hH hs
  have hconst : Tendsto suzukiProposition118SourceQPairing atTop
      (𝓝 (suzukiProposition118SourceQPairing 2)) :=
    tendsto_const_nhds.congr' hev.symm
  have htwo : suzukiProposition118SourceQPairing 2 = 0 :=
    tendsto_nhds_unique hconst (tendsto_suzukiProposition118SourceQPairing_zero hH)
  rw [suzukiProposition118SourceQPairing_eq_lowerBoundary hH hy, htwo]

/-- Suzuki's lower-boundary constant is zero, now closed from the genuine source
pairing rather than assumed. -/
theorem suzukiLowerBoundaryLimit_eq_zero_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    suzukiLowerBoundaryLimit = 0 := by
  have hp := suzukiProposition118SourceQPairing_zero hH (y := (2 : ℝ)) (by norm_num)
  rw [suzukiProposition118SourceQPairing_at_lowerBoundary hH,
    suzukiProposition118LowerBoundaryPairingScalar_eq_neg] at hp
  linarith

/-- Equivalently, the even source mass at the lower boundary is normalized to
one. -/
theorem suzukiProposition118SourceTMinus_at_two_eq_one
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    suzukiProposition118SourceTMinus 2 = 1 := by
  rw [suzukiProposition118SourceTMinus_eq]
  exact suzukiLowerBoundaryLimit_eq_zero_iff.mp
    (suzukiLowerBoundaryLimit_eq_zero_of_sourceContract hH)


end MathlibNt.SieveTheory
