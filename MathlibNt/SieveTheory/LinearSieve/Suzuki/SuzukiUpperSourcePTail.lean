import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePairingWindowTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourcePairingFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEinEulerTailAsymptotic
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiStandardUpperAdjointDDE
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSecondIntervalJurkatRichertBridge

/-!
# Tail of Suzuki's genuine upper source

The two nonnegative parity source tails are dominated by their sum `Q`, whose
exponential decay was already obtained from the Section 13 source contract.
Consequently the genuine upper source tends to `2`.
-/

namespace MathlibNt.SieveTheory

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Interval
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- The genuine source sum `Q=T⁺+T⁻` tends to zero. -/
theorem tendsto_suzukiProposition118SourceQ_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiProposition118SourceQ atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    suzukiProposition118SourceQ_eventually_le_mul_exp hH
  apply squeeze_zero' (hbound.mono fun _ hs => hs.1)
    (hbound.mono fun _ hs => hs.2)
  simpa [mul_assoc] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul D

/-- Each parity source tail tends to zero separately. -/
theorem tendsto_suzukiProposition118Source_parity_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiProposition118SourceTPlus atTop (𝓝 0) ∧
      Tendsto suzukiProposition118SourceTMinus atTop (𝓝 0) := by
  obtain ⟨C, hC, hseries⟩ := suzukiProposition118SourceParitySeries_le_hat hH
  rcases hH.t5 .plus with ⟨Cp, hCp, hp⟩
  rcases hH.t5 .minus with ⟨Cm, hCm, hm⟩
  constructor
  · apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
      exact tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith))
    · filter_upwards [eventually_ge_atTop (2 : ℝ), hp] with s hs hhat
      have hT := (hseries s hs).1
      have hs0 : 0 ≤ s := by linarith
      have hhat0 := (hH.positive .plus s (by linarith : 0 < s)).le
      calc
        suzukiProposition118SourceTPlus s ≤ C * s * H.T .plus s := hT
        _ ≤ C * s * (Cp * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left
            (by simpa [abs_of_nonneg hhat0] using hhat)
            (mul_nonneg hC hs0)
        _ = (C * Cp) * (s ^ 1 * Real.exp (-s)) := by ring
    · simpa using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (C * Cp)
  · apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
      exact tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg hs k)
    · filter_upwards [eventually_ge_atTop (2 : ℝ), hm] with s hs hhat
      have hT := (hseries s hs).2
      have hs0 : 0 ≤ s := by linarith
      have hhat0 := (hH.positive .minus s (by linarith : 0 < s)).le
      calc
        suzukiProposition118SourceTMinus s ≤ C * s * H.T .minus s := hT
        _ ≤ C * s * (Cm * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left
            (by simpa [abs_of_nonneg hhat0] using hhat)
            (mul_nonneg hC hs0)
        _ = (C * Cm) * (s ^ 1 * Real.exp (-s)) := by ring
    · simpa using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (C * Cm)

/-- On the closed series range the history-defined upper source agrees with
`2 + T⁺ - T⁻`.  The endpoint uses the already proved source-pairing consequence
`T⁻(2)=1`; this is exactly the boundary compatibility needed below. -/
private theorem suzukiUpperSourceP_eq_series
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiUpperSourceP s =
      2 + suzukiProposition118SourceTPlus s -
        suzukiProposition118SourceTMinus s := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [suzukiUpperSourceP_of_le_two (by norm_num),
      suzukiProposition118SourceTMinus_at_two_eq_one hH]
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      (s := (2 : ℝ)) (by norm_num) (by norm_num)
    field_simp
    linarith
  · rw [suzukiUpperSourceP_of_two_lt hs, suzukiContinuousLowerTail]

/-- On a post-threshold interval both shifted parity tails are integrable. -/
private theorem suzukiUpperSourceParity_shift_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => suzukiProposition118SourceTPlus (t - 1)) volume x y ∧
      IntervalIntegrable (fun t => suzukiProposition118SourceTMinus (t - 1)) volume x y := by
  have hQ := suzukiProposition118SourceQ_shift_intervalIntegrable hH
    (by linarith : 2 ≤ x) hxy
  have hlayer : ∀ n : ℕ, AEStronglyMeasurable
      (fun t => suzukiLayer 1 2 n (t - 1)) (volume.restrict (Set.uIoc x y)) := by
    intro n
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    have hr := (KappaOneModel.regular (by norm_num : (1 : ℝ) < 2) n).continuous
    apply (hr.comp (continuousOn_id.sub continuousOn_const) ?_).congr
      (fun t _ => (KappaOneModel.layer_eq_suzukiLayer 2 n (t - 1)).symm)
    intro t ht
    unfold KappaOneModel.closedDomain KappaOneModel.eps
    simp only [Set.mem_Ici]
    rw [Set.mem_uIoc] at ht
    have heps : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 2)))
    dsimp
    rcases ht with ht | ht <;> linarith
  have hpmeas : AEStronglyMeasurable
      (fun t => suzukiProposition118SourceTPlus (t - 1))
      (volume.restrict (Set.uIoc x y)) :=
    AEStronglyMeasurable.tsum (fun k => hlayer (2 * k + 1))
  have hmmeas : AEStronglyMeasurable
      (fun t => suzukiProposition118SourceTMinus (t - 1))
      (volume.restrict (Set.uIoc x y)) :=
    AEStronglyMeasurable.tsum (fun k => hlayer (2 * (k + 1)))
  constructor
  · apply hQ.mono_fun hpmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.mem_uIoc] at ht
    have ht2 : 2 ≤ t - 1 := by rcases ht with ht | ht <;> linarith
    have hp0 : 0 ≤ suzukiProposition118SourceTPlus (t - 1) :=
      tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith))
    have hm0 : 0 ≤ suzukiProposition118SourceTMinus (t - 1) :=
      tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg ht2 k)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0,
      suzukiProposition118SourceQ, if_neg (not_lt.mpr ht2),
      abs_of_nonneg (add_nonneg hp0 hm0)]
    linarith
  · apply hQ.mono_fun hmmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.mem_uIoc] at ht
    have ht2 : 2 ≤ t - 1 := by rcases ht with ht | ht <;> linarith
    have hp0 : 0 ≤ suzukiProposition118SourceTPlus (t - 1) :=
      tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith))
    have hm0 : 0 ≤ suzukiProposition118SourceTMinus (t - 1) :=
      tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg ht2 k)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm0,
      suzukiProposition118SourceQ, if_neg (not_lt.mpr ht2),
      abs_of_nonneg (add_nonneg hp0 hm0)]
    linarith

private theorem suzukiUpperSourceP_shift_intervalIntegrable_of_le_three
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3) :
    IntervalIntegrable (fun t => suzukiUpperSourceP (t - 1)) volume x y := by
  have hc : ContinuousOn
      (fun t : ℝ => suzukiLowerSieveAmplitude / (t - 1)) (Set.uIcc x y) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact ne_of_gt (by linarith [hx, ht.1] : 0 < t - 1)
  apply hc.intervalIntegrable.congr
  intro t ht
  rw [uIoc_of_le hxy] at ht
  change suzukiLowerSieveAmplitude / (t - 1) = suzukiUpperSourceP (t - 1)
  rw [suzukiUpperSourceP_of_le_two (by linarith [ht.2, hy] : t - 1 ≤ 2)]

private theorem suzukiUpperSourceP_shift_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => suzukiUpperSourceP (t - 1)) volume x y := by
  by_cases hy : y ≤ 3
  · exact suzukiUpperSourceP_shift_intervalIntegrable_of_le_three hx hxy hy
  by_cases hx3 : 3 ≤ x
  · rcases suzukiUpperSourceParity_shift_intervalIntegrable hH hx3 hxy with ⟨hp, hm⟩
    have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume x y :=
      intervalIntegrable_const
    apply (hc.add hp).sub hm |>.congr
    intro t ht
    rw [uIoc_of_le hxy] at ht
    change 2 + suzukiProposition118SourceTPlus (t - 1) -
      suzukiProposition118SourceTMinus (t - 1) = suzukiUpperSourceP (t - 1)
    rw [suzukiUpperSourceP_eq_series hH (by linarith [hx3, ht.1] : 2 ≤ t - 1)]
  · have hx3' : x ≤ 3 := le_of_not_ge hx3
    have h3y : 3 ≤ y := le_of_not_ge hy
    exact (suzukiUpperSourceP_shift_intervalIntegrable_of_le_three hx hx3' le_rfl).trans
      (by
        rcases suzukiUpperSourceParity_shift_intervalIntegrable hH le_rfl h3y with ⟨hp, hm⟩
        apply (intervalIntegrable_const.add hp).sub hm |>.congr
        intro t ht
        rw [uIoc_of_le h3y] at ht
        change 2 + suzukiProposition118SourceTPlus (t - 1) -
          suzukiProposition118SourceTMinus (t - 1) = suzukiUpperSourceP (t - 1)
        rw [suzukiUpperSourceP_eq_series hH (by linarith [ht.1] : 2 ≤ t - 1)])

private theorem suzukiUpperSourceP_weighted_sub_of_le_three
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3) :
    y * suzukiUpperSourceP y - x * suzukiUpperSourceP x =
      ∫ t in x..y, suzukiUpperSourceP (t - 1) := by
  have hminus := suzukiProposition118SourceTMinus_weighted_sub hH hx hxy
  have hplusInt : IntervalIntegrable
      (fun t => suzukiProposition118SourceTPlus (t - 1)) volume x y := by
    have hc : ContinuousOn
        (fun t : ℝ => suzukiLowerSieveAmplitude / (t - 1) - 1) (Set.uIcc x y) := by
      apply (continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_).sub
        continuousOn_const
      intro t ht
      rw [uIcc_of_le hxy] at ht
      exact ne_of_gt (by linarith [hx, ht.1] : 0 < t - 1)
    apply hc.intervalIntegrable.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).2
    have hne2 : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (μ := volume) (2 : ℝ))
    filter_upwards [hne2] with t ht2
    intro ht
    rw [uIoc_of_le hxy] at ht
    have ht1 : 1 < t - 1 := lt_of_le_of_ne (by linarith [hx, ht.1] : 1 ≤ t - 1)
      (fun h => ht2 (by linarith))
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      ht1 (by linarith [ht.2, hy] : t - 1 ≤ 3)
    field_simp [ne_of_gt (by linarith : 0 < t - 1)] at hp ⊢
    linarith
  have hIntegral :
      (∫ t in x..y, suzukiUpperSourceP (t - 1)) =
        (y - x) + ∫ t in x..y, suzukiProposition118SourceTPlus (t - 1) := by
    have hone : (∫ _t in x..y, (1 : ℝ)) = y - x := by simp
    rw [← hone, ← intervalIntegral.integral_add intervalIntegrable_const hplusInt]
    apply intervalIntegral.integral_congr_ae
    have hne2 : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (μ := volume) (2 : ℝ))
    filter_upwards [hne2] with t ht2
    intro ht
    rw [uIoc_of_le hxy] at ht
    have ht1 : 1 < t - 1 := lt_of_le_of_ne (by linarith [hx, ht.1] : 1 ≤ t - 1)
      (fun h => ht2 (by linarith))
    rw [suzukiUpperSourceP_of_le_two (by linarith [ht.2, hy] : t - 1 ≤ 2)]
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      ht1 (by linarith [ht.2, hy] : t - 1 ≤ 3)
    field_simp [ne_of_gt (by linarith : 0 < t - 1)] at hp ⊢
    linarith
  have hweighted (s : ℝ) (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
      s * suzukiUpperSourceP s =
        suzukiLowerSieveAmplitude + s -
          s * suzukiProposition118SourceTMinus s := by
    rw [suzukiUpperSourceP_eq_series hH hs2]
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      (by linarith : 1 < s) hs3
    linarith
  rw [hweighted y (hx.trans hxy) hy, hweighted x hx (hxy.trans hy), hIntegral]
  linarith

private theorem suzukiUpperSourceP_weighted_sub_of_three_le
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    y * suzukiUpperSourceP y - x * suzukiUpperSourceP x =
      ∫ t in x..y, suzukiUpperSourceP (t - 1) := by
  have hp := suzukiProposition118SourceTPlus_weighted_sub hH hx hxy
  have hm := suzukiProposition118SourceTMinus_weighted_sub hH (by linarith : 2 ≤ x) hxy
  rcases suzukiUpperSourceParity_shift_intervalIntegrable hH hx hxy with ⟨hpint, hmint⟩
  have hIntegral :
      (∫ t in x..y, suzukiUpperSourceP (t - 1)) =
        2 * (y - x) +
          (∫ t in x..y, suzukiProposition118SourceTPlus (t - 1)) -
          ∫ t in x..y, suzukiProposition118SourceTMinus (t - 1) := by
    have htwo : (∫ _t in x..y, (2 : ℝ)) = 2 * (y - x) := by simp; ring
    calc
      (∫ t in x..y, suzukiUpperSourceP (t - 1)) =
          ∫ t in x..y, (2 + suzukiProposition118SourceTPlus (t - 1) -
            suzukiProposition118SourceTMinus (t - 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hxy] at ht
        change suzukiUpperSourceP (t - 1) =
          2 + suzukiProposition118SourceTPlus (t - 1) -
            suzukiProposition118SourceTMinus (t - 1)
        rw [suzukiUpperSourceP_eq_series hH
          (by linarith [hx, ht.1] : 2 ≤ t - 1)]
      _ = (∫ _t in x..y, (2 : ℝ)) +
            (∫ t in x..y, suzukiProposition118SourceTPlus (t - 1)) -
            ∫ t in x..y, suzukiProposition118SourceTMinus (t - 1) := by
        rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hpint) hmint,
          intervalIntegral.integral_add intervalIntegrable_const hpint]
      _ = _ := by rw [htwo]
  rw [suzukiUpperSourceP_eq_series hH (by linarith : 2 ≤ y),
    suzukiUpperSourceP_eq_series hH (by linarith : 2 ≤ x), hIntegral]
  linarith

/-- The genuine upper source satisfies its forward integral DDE on every
`2 ≤ x ≤ y`, including both the switching endpoint and intervals crossing
`s=3`. -/
theorem suzukiUpperSourceP_weighted_sub
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    y * suzukiUpperSourceP y - x * suzukiUpperSourceP x =
      ∫ t in x..y, suzukiUpperSourceP (t - 1) := by
  by_cases hy : y ≤ 3
  · exact suzukiUpperSourceP_weighted_sub_of_le_three hH hx hxy hy
  by_cases hx3 : 3 ≤ x
  · exact suzukiUpperSourceP_weighted_sub_of_three_le hH hx3 hxy
  · have hx3' : x ≤ 3 := le_of_not_ge hx3
    have h3y : 3 ≤ y := le_of_not_ge hy
    have hlo := suzukiUpperSourceP_weighted_sub_of_le_three hH hx hx3' le_rfl
    have hhi := suzukiUpperSourceP_weighted_sub_of_three_le hH le_rfl h3y
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (suzukiUpperSourceP_shift_intervalIntegrable_of_le_three hx hx3' le_rfl)
      (suzukiUpperSourceP_shift_intervalIntegrable hH (by norm_num) h3y)
    linarith

private theorem continuousOn_weighted_suzukiUpperSourceP
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {M : ℝ} (hM : 2 ≤ M) :
    ContinuousOn (fun s => s * suzukiUpperSourceP s) (Icc 2 M) := by
  let f : ℝ → ℝ := fun t => suzukiUpperSourceP (t - 1)
  have hf := suzukiUpperSourceP_shift_intervalIntegrable hH
    (x := (2 : ℝ)) (y := M) (by norm_num) hM
  have hprim := intervalIntegral.continuousOn_primitive
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hM).1 hf)
  have hc : ContinuousOn
      (fun s => 2 * suzukiUpperSourceP 2 + ∫ t in Ioc 2 s, f t)
      (Icc 2 M) := continuousOn_const.add hprim
  apply hc.congr
  intro s hs
  have hd := suzukiUpperSourceP_weighted_sub hH
    (x := (2 : ℝ)) (y := s) (by norm_num) hs.1
  rw [intervalIntegral.integral_of_le hs.1] at hd
  dsimp [f]
  linarith

private theorem continuousOn_suzukiUpperSourceP
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ContinuousOn suzukiUpperSourceP (Ici (1 : ℝ)) := by
  intro s hs
  change 1 ≤ s at hs
  rcases lt_trichotomy s 2 with hs2 | rfl | hs2
  · have hr : ContinuousAt (fun u : ℝ => suzukiLowerSieveAmplitude / u) s :=
      continuousAt_const.div continuousAt_id (ne_of_gt (by linarith : 0 < s))
    apply hr.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hs2)] with u hu
      rw [suzukiUpperSourceP_of_le_two hu.le]
    · rw [suzukiUpperSourceP_of_le_two hs2.le]
  · have hr : ContinuousAt (fun u : ℝ => suzukiLowerSieveAmplitude / u) 2 :=
      continuousAt_const.div continuousAt_id (by norm_num)
    have hlo : ContinuousWithinAt suzukiUpperSourceP (Iic (2 : ℝ)) 2 := by
      apply hr.continuousWithinAt.congr
      · intro u hu
        exact suzukiUpperSourceP_of_le_two hu
      · exact suzukiUpperSourceP_of_le_two le_rfl
    have hW := continuousOn_weighted_suzukiUpperSourceP hH
      (M := (3 : ℝ)) (by norm_num)
    have hWsmall : ContinuousWithinAt
        (fun u => u * suzukiUpperSourceP u) (Icc (2 : ℝ) 3) 2 :=
      hW.continuousWithinAt ⟨le_rfl, by norm_num⟩
    have hsets : Icc (2 : ℝ) 3 =ᶠ[𝓝 (2 : ℝ)] Ici 2 := by
      filter_upwards [Iio_mem_nhds (by norm_num : (2 : ℝ) < 3)] with u hu
      apply propext
      change (2 ≤ u ∧ u ≤ 3) ↔ 2 ≤ u
      exact ⟨fun h => h.1, fun h => ⟨h, hu.le⟩⟩
    have hWright : ContinuousWithinAt
        (fun u => u * suzukiUpperSourceP u) (Ici (2 : ℝ)) 2 :=
      hWsmall.congr_set hsets
    have hdiv := hWright.div continuousWithinAt_id (by norm_num : (2 : ℝ) ≠ 0)
    have hhi : ContinuousWithinAt suzukiUpperSourceP (Ici (2 : ℝ)) 2 := by
      apply hdiv.congr
      · intro u hu
        change 2 ≤ u at hu
        change suzukiUpperSourceP u = (u * suzukiUpperSourceP u) / u
        field_simp [ne_of_gt (by linarith : 0 < u)]
      · norm_num
    have hall := hlo.union hhi
    have hat : ContinuousAt suzukiUpperSourceP 2 := by
      simpa only [Iic_union_Ici, continuousWithinAt_univ] using hall
    exact hat.continuousWithinAt
  · have hW := continuousOn_weighted_suzukiUpperSourceP hH
      (M := s + 1) (by linarith)
    have hWat := hW.continuousAt (Icc_mem_nhds hs2 (by linarith : s < s + 1))
    have hdiv := hWat.div continuousAt_id (ne_of_gt (by linarith : 0 < s))
    apply hdiv.continuousWithinAt.congr
    · intro u hu
      change 1 ≤ u at hu
      change suzukiUpperSourceP u = (u * suzukiUpperSourceP u) / u
      field_simp [ne_of_gt (by linarith : 0 < u)]
    · change suzukiUpperSourceP s = (s * suzukiUpperSourceP s) / s
      field_simp [ne_of_gt (by linarith : 0 < s)]

/-- Closed production integral-DDE package for the genuine upper source. -/
theorem suzukiUpperSourceP_integralDDE_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SuzukiUpperSourcePIntegralDDE :=
  ⟨continuousOn_suzukiUpperSourceP hH,
    fun _ _ hx hxy => suzukiUpperSourceP_weighted_sub hH hx hxy⟩

/-- The actual upper source tends to its Proposition 11.8 terminal value `2`. -/
theorem suzukiUpperSourceP_tail_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SuzukiUpperSourcePTail := by
  rcases tendsto_suzukiProposition118Source_parity_zero hH with ⟨hp, hm⟩
  unfold SuzukiUpperSourcePTail
  have htail : Tendsto (fun s : ℝ =>
      2 + suzukiProposition118SourceTPlus s -
        suzukiProposition118SourceTMinus s) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add hp |>.sub hm
  apply htail.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  rw [suzukiUpperSourceP_of_two_lt hs, suzukiContinuousLowerTail]

/-- The genuine moving-window tail follows without any additional analytic
premise. -/
theorem suzukiUpperSourcePairingWindowTail_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SuzukiUpperSourcePairingWindowTail :=
  suzukiUpperSourcePairingWindowTail_of_sourceTail
    (suzukiUpperSourceP_tail_of_sourceContract hH)

/-- The Section-13 source contract now supplies every source-side input to the
upper pairing, so the pairing is identically `2` on its legal range. -/
theorem suzukiUpperSourcePairing_eq_two_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiUpperSourcePairing suzukiStandardUpperAdjoint s = 2 := by
  apply suzukiUpperSourcePairing_eq_two
    (suzukiUpperSourceP_integralDDE_of_sourceContract hH)
  · intro u hu
    exact suzukiStandardUpperAdjoint_hasDerivAt_dde (by linarith)
  · exact suzukiUpperSourceP_tail_of_sourceContract hH
  · exact suzukiStandardUpperAdjoint_scaledTail
  · exact suzukiUpperSourcePairingWindowTail_of_sourceContract hH
  · exact hs

/-- Final amplitude normalization for Suzuki's genuine production source. -/
theorem suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    suzukiLowerSieveAmplitude =
      2 * Real.exp Real.eulerMascheroniConstant := by
  have hp : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt suzukiStandardUpperAdjoint
        (-suzukiStandardUpperAdjoint (t + 1) / t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    exact suzukiStandardUpperAdjoint_hasDerivAt_dde (by linarith [ht.1])
  have hpOn : ContinuousOn suzukiStandardUpperAdjoint (Ici (2 : ℝ)) := by
    intro t ht
    change 2 ≤ t at ht
    exact (suzukiStandardUpperAdjoint_hasDerivAt_dde
      (by linarith : 0 < t)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun t => suzukiStandardUpperAdjoint (t + 1) / t) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact hpOn.comp (continuousOn_id.add continuousOn_const) (by
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        simp only [Set.mem_Ici]
        linarith [ht.1])
    · exact continuousOn_id
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact ne_of_gt (by linarith [ht.1] : 0 < t)
  exact suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_upperPairing
    hp hint (suzukiUpperSourcePairing_eq_two_of_sourceContract hH (by norm_num))
    suzukiStandardUpperAdjoint_one_eq_exp_neg_eulerMascheroni_unconditional

/-- On `4 ≤ s ≤ 6`, the normalized source formula is exactly the standard
Jurkat--Richert dimension-one lower sieve factor. -/
theorem suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs₄ : 4 ≤ s) (hs₆ : s ≤ 6) :
    suzukiContinuousLowerFactor s =
      SwitchingPrinciple.dimensionOneLowerLinearSieveFactor s :=
  suzukiContinuousLowerFactor_eq_dimensionOne_conditional hH
    (suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract hH)
    hs₄ hs₆


end MathlibNt.SieveTheory
