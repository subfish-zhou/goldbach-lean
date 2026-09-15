import MathlibNt.Wu2008DoubleSieve.ImprovementIntegrals

/-!
# Uniform finite-threshold coefficients and the inner integral limit

The same baseline threshold works for every source parameter in the bounded
interval. This gives actual finite-threshold coefficient monotonicity and
integrability uniformly in that parameter, before taking N0 to infinity.
Together with the separate depth-limit theorem this preserves Wu's order
of limits in the integrals following (3.20).
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory
open scoped Classical Topology Interval

theorem wuImprovement_uniform_base_exists (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧
      (∀ s : ℝ, 1 ≤ s → s ≤ 10 → -1 ∈ wuAdmissibleImprovements upper k δ s T) ∧
      ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
        wuSourceBox k δ N i Δ V →
        0 < boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hbase : ∃ M : ℕ, ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      -1 ∈ wuAdmissibleImprovements upper k δ s M := by
    cases upper
    · obtain ⟨M, hM⟩ := wu_boxPhi_lower_source_bounded k hk hδ hδhi (ε := 1) (by norm_num)
      refine ⟨M, ?_⟩
      intro s hs hs10 N hN _ he i Δ V hb
      simpa [wuImprovementComparison, wuLowerCoefficient, sub_eq_add_neg] using
        (hM N hN he i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.1
          hb.2.2.2.2.1 hb.2.2.2.2.2 s hs hs10).2
    · obtain ⟨M, hM⟩ := wu_boxPhi_upper_source_bounded k hk hδ hδhi (ε := 1) (by norm_num)
      refine ⟨M, ?_⟩
      intro s hs hs10 N hN _ he i Δ V hb
      simpa [wuImprovementComparison, wuUpperCoefficient] using
        (hM N hN he i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.1
          hb.2.2.2.2.1 hb.2.2.2.2.2 s hs hs10).1
  obtain ⟨M, hM⟩ := hbase
  obtain ⟨c, hc, L, hL⟩ := wu_boxTheta_lower k hδ hδhi
  refine ⟨max 4 (max M L), le_max_left _ _, ?_, ?_⟩
  · intro s hs hs10
    exact wuAdmissibleImprovements_mono_threshold upper k δ s
      ((le_max_left M L).trans (le_max_right _ _)) (hM s hs hs10)
  · intro N hN i Δ V hb
    have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
    have hNL : L ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    exact (by positivity : 0 < c * (N : ℝ) / log N ^ (5 * k + 2)).trans_le
      (hL N hNL i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.2.1 hb.2.2.2.2.2)

/-- A single threshold, chosen before s, supplies nonemptiness, attainment
and a lower bound for all finite-threshold suprema on the parameter interval. -/
theorem wuImprovementAt_uniform_eventually_attained (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop, ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      (wuAdmissibleImprovements upper k δ s N0).Nonempty ∧
      wuImprovementAt upper k δ s N0 ∈ wuAdmissibleImprovements upper k δ s N0 ∧
      -1 ≤ wuImprovementAt upper k δ s N0 := by
  obtain ⟨T, _, hT, hθ⟩ := wuImprovement_uniform_base_exists upper k hk hδ hδhi
  filter_upwards [eventually_ge_atTop T] with N0 hN0
  intro s hs hs10
  have hmem := wuAdmissibleImprovements_mono_threshold upper k δ s hN0 (hT s hs hs10)
  have hne : (wuAdmissibleImprovements upper k δ s N0).Nonempty := ⟨-1, hmem⟩
  have hsub : wuAdmissibleImprovements upper k δ s N0 ⊆ wuEventualImprovements upper k δ s :=
    fun _ hh => ⟨N0, hh⟩
  refine ⟨hne, wuImprovementAt_mem_of_positive_theta upper hne
    (fun N hN _ _ i Δ V hb => hθ N (hN0.trans hN) i Δ V hb), ?_⟩
  exact le_csSup ((wuEventualImprovements_bddAbove upper k hδ hδhi hs hs10).mono hsub) hmem

/-- Uniform parameter monotonicity at finite threshold, not a threshold
selected separately for each pair of source parameters. -/
theorem wu_effective_threshold_uniform_monotone (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop,
      MonotoneOn (fun s => if upper then wuUpperCoefficient s - wuImprovementAt upper k δ s N0
        else wuLowerCoefficient s + wuImprovementAt upper k δ s N0) (Icc 1 10) := by
  filter_upwards [wuImprovementAt_uniform_eventually_attained upper k hk hδ hδhi] with N0 hN0
  intro s hs t ht hst
  have hsub : ∀ x : ℝ, wuAdmissibleImprovements upper k δ x N0 ⊆
      wuEventualImprovements upper k δ x := fun _ _ hh => ⟨N0, hh⟩
  cases upper
  · have hm := wuAdmissibleImprovements_lower_shift hδ hδhi hs.1 hst (hN0 s hs.1 hs.2).2.1
    have hbound := le_csSup
      ((wuEventualImprovements_bddAbove false k hδ hδhi ht.1 ht.2).mono (hsub t)) hm
    change _ ≤ wuImprovementAt false k δ t N0 at hbound
    simp only [Bool.false_eq_true, if_false]
    linarith
  · have hm := wuAdmissibleImprovements_upper_shift hδ hδhi hs.1 hst (hN0 t ht.1 ht.2).2.1
    have hbound := le_csSup
      ((wuEventualImprovements_bddAbove true k hδ hδhi hs.1 hs.2).mono (hsub s)) hm
    change _ ≤ wuImprovementAt true k δ s N0 at hbound
    simp only [if_true]
    linarith

theorem wuImprovementAt_eventually_intervalIntegrable (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    ∀ᶠ N0 : ℕ in atTop,
      IntervalIntegrable (fun t => wuImprovementAt upper k δ t N0 / t) volume a b := by
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < a) hx.1
  have hsub' : uIcc a b ⊆ Icc (1 : ℝ) 10 := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc a b) :=
    continuousOn_id.inv₀ (fun t ht => (hsub ht).ne')
  filter_upwards [wu_effective_threshold_uniform_monotone upper k hk hδ hδhi] with N0 hN0
  have hraw : IntervalIntegrable (fun t => wuImprovementAt upper k δ t N0) volume a b := by
    cases upper
    · have hm : MonotoneOn (fun s => wuLowerCoefficient s +
          wuImprovementAt false k δ s N0) (uIcc a b) := by
        simpa using hN0.mono hsub'
      have hi := hm.intervalIntegrable (μ := volume)
      have hc := (continuousOn_wuLowerCoefficient.mono hsub).intervalIntegrable (μ := volume)
      convert hi.sub hc using 1
      ext s
      ring
    · have hm : MonotoneOn (fun s => wuUpperCoefficient s -
          wuImprovementAt true k δ s N0) (uIcc a b) := by
        simpa using hN0.mono hsub'
      have hi := hm.intervalIntegrable (μ := volume)
      have hc := (continuousOn_wuUpperCoefficient.mono hsub).intervalIntegrable (μ := volume)
      convert hc.sub hi using 1
      ext s
      ring
  simpa only [div_eq_mul_inv] using hraw.mul_continuousOn hinv

theorem wuImprovementAt_uniform_div_norm_bound (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop, ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      ‖wuImprovementAt upper k δ s N0 / s‖ ≤ 10 := by
  filter_upwards [wuImprovementAt_uniform_eventually_attained upper k hk hδ hδhi] with N0 hN0
  intro s hs hs10
  have hs0 : 0 < s := by linarith
  have hlow := (hN0 s hs hs10).2.2
  have hE : wuImprovementAt upper k δ s N0 ∈ wuEventualImprovements upper k δ s :=
    ⟨N0, (hN0 s hs hs10).2.1⟩
  have hup := le_csSup (wuEventualImprovements_bddAbove upper k hδ hδhi hs hs10) hE
  have hdiv : wuImprovementAt upper k δ s N0 / s ≤
      wuImprovementAtInfinity upper k δ s / s := div_le_div_of_nonneg_right hup hs0.le
  have hnorm := wuImprovementAtInfinity_div_norm_le_ten upper k hk hδ hδhi hs hs10
  rw [Real.norm_eq_abs] at hnorm ⊢
  apply abs_le.2
  constructor
  · apply (le_div_iff₀ hs0).2
    linarith
  · exact hdiv.trans ((le_abs_self _).trans hnorm)

/-- The inner threshold limit passes through the actual source integral
at fixed depth, before the separate outer depth limit is taken. -/
theorem wuImprovement_integral_threshold_limit (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    Tendsto (fun N0 : ℕ => ∫ t in a..b, wuImprovementAt upper k δ t N0 / t)
      atTop (𝓝 (∫ t in a..b, wuImprovementAtInfinity upper k δ t / t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 10)
  · filter_upwards [wuImprovementAt_eventually_intervalIntegrable upper k hk hδ hδhi ha hab hb]
      with N0 hN0
    exact hN0.def'.aestronglyMeasurable
  · filter_upwards [wuImprovementAt_uniform_div_norm_bound upper k hk hδ hδhi] with N0 hN0
    apply ae_of_all
    intro t ht
    rw [uIoc_of_le hab] at ht
    exact hN0 t (ha.trans ht.1.le) (ht.2.trans hb)
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro t ht
    rw [uIoc_of_le hab] at ht
    exact (wuImprovementAt_tendsto upper k hk hδ hδhi
      (ha.trans ht.1.le) (ht.2.trans hb)).div_const t

end Wu2008DoubleSieve
