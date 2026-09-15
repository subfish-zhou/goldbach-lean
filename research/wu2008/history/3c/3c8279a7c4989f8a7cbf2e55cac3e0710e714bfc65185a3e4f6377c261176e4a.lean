import MathlibNt.Wu2008DoubleSieve.ReboxingUpperNormalization
import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeIntegral
import MathlibNt.Wu2008DoubleSieve.ImprovementEffectiveIntegrals

/-!
# The upper raw estimate and the first actual Wu08 (3.8) inequality

Wu04 (3.16)--(3.20): the proved raw upper estimate improves the lower
source coefficient. The threshold tends to infinity at fixed depth
before the depth tends to infinity. No raw estimate or cross inequality
is a hypothesis.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology Interval

theorem reboxingRawPrimeSum_upper_integral (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
          ((∫ u in (s - 1)..(t - 1), wuEffectiveCoefficient true (k + 1) δ N0 u / u) +
            ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hT1⟩ := reboxingRawPrimeSum_upper_prime k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := wu_reboxing_prime_integral_relative true k hδ
    (by linarith : δ < 1 / 2) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he i Δ V hb s t hs hst ht
  have h2 := (abs_le.mp
    (hT2 N0 ((le_max_right _ _).trans hN0) N hN i Δ V hb s t hs hst ht)).2
  nlinarith

theorem wuImprovementAt_lower_cross_eventually (k : ℕ) (hk : 1 ≤ k)
    {δ s t ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hε : 0 < ε) :
    ∀ᶠ N0 : ℕ in atTop,
      wuImprovementAt false k δ t N0 +
        (∫ u in (s - 1)..(t - 1), wuImprovementAt true (k + 1) δ u N0 / u) - ε ≤
      wuImprovementAt false k δ s N0 := by
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨T, _, hT⟩ := reboxingRawPrimeSum_upper_integral k hδ hδhi hε
  filter_upwards [eventually_ge_atTop T,
    wuImprovementAt_eventually_attained false k hk hδ hδhalf (by linarith) ht,
    wuEffectiveCoefficient_integral_eventually true (k + 1) (by omega)
      hδ hδhalf hs hst ht] with N0 hN0 hatt hint
  have hmem : wuImprovementAt false k δ t N0 +
        (∫ u in (s - 1)..(t - 1), wuImprovementAt true (k + 1) δ u N0 / u) - ε ∈
      wuAdmissibleImprovements false k δ s N0 := by
    intro N hN hN4 he i Δ V hb
    have hraw := hT N0 hN0 N hN he i Δ V hb s t hs hst ht
    rw [hint] at hraw
    simp only [if_true] at hraw
    have hbase := hatt.2 N hN hN4 he i Δ V hb
    have hbuch := wuBoxPhi_buchstab (convolutionWuWindows N Δ V)
      (fun d hd => (wu_buchstab_prime_window_bounds (by omega) hδ hδhalf
        hb hs hst ht hd).2.2.1.le) (by linarith : 0 < s) hst
    change wuBoxPhi N δ (convolutionWuWindows N Δ V) t =
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s +
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) at hbuch
    change (wuLowerCoefficient t + wuImprovementAt false k δ t N0) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _ at hbase
    change (wuLowerCoefficient s + _) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _
    nlinarith
  have hsub : wuAdmissibleImprovements false k δ s N0 ⊆
      wuEventualImprovements false k δ s := fun _ hh => ⟨N0, hh⟩
  exact le_csSup ((wuEventualImprovements_bddAbove false k hδ hδhalf
    (by linarith : 1 ≤ s) (hst.trans ht)).mono hsub) hmem

theorem wuImprovementAtInfinity_lower_cross (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    wuImprovementAtInfinity false k δ t +
      (∫ u in (s - 1)..(t - 1), wuImprovementAtInfinity true (k + 1) δ u / u) ≤
    wuImprovementAtInfinity false k δ s := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hsconv := wuImprovementAt_tendsto false k hk hδ hδhalf
    (show 1 ≤ s by linarith) (hst.trans ht)
  have htconv := wuImprovementAt_tendsto false k hk hδ hδhalf
    (show 1 ≤ t by linarith) ht
  have hiconv := wuImprovement_integral_threshold_limit true (k + 1) (by omega)
    hδ hδhalf (show 1 ≤ s - 1 by linarith)
    (show s - 1 ≤ t - 1 by linarith) (show t - 1 ≤ 10 by linarith)
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := le_of_tendsto_of_tendsto ((htconv.add hiconv).sub_const ε) hsconv
    (wuImprovementAt_lower_cross_eventually k hk hδ hδhi hs hst ht hε)
  linarith

/-- Wu08 (3.8), first inequality, for the actual limiting source gains. -/
theorem wuImprovementLimit_lower_cross {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    wuImprovementLimit false δ t +
      (∫ u in (s - 1)..(t - 1), wuImprovementLimit true δ u / u) ≤
    wuImprovementLimit false δ s := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hsconv := wuImprovementAtInfinity_tendsto false hδ hδhalf
    (show 1 ≤ s by linarith) (hst.trans ht)
  have htconv := wuImprovementAtInfinity_tendsto false hδ hδhalf
    (show 1 ≤ t by linarith) ht
  have hiconv := (wuImprovement_integral_depth_limit true hδ hδhalf
    (show 1 ≤ s - 1 by linarith) (show s - 1 ≤ t - 1 by linarith)
    (show t - 1 ≤ 10 by linarith)).comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto (htconv.add hiconv) hsconv
    (Eventually.of_forall fun k =>
      wuImprovementAtInfinity_lower_cross (k + 1) (by omega) hδ hδhi hs hst ht)

theorem wuImprovementLimit_lower_antitone {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    AntitoneOn (wuImprovementLimit false δ) (Set.Icc 2 10) := by
  intro s hs t ht hst
  have hcross := wuImprovementLimit_lower_cross hδ hδhi hs.1 hst ht.2
  have hi : 0 ≤ ∫ u in (s - 1)..(t - 1), wuImprovementLimit true δ u / u := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    have hu1 : 1 ≤ u := by linarith [hs.1, hu.1]
    exact div_nonneg (wuImprovementLimit_nonneg true hδ (by linarith : δ < 1 / 2)
      hu1 (by linarith [hu.2, ht.2])) (by linarith)
  linarith

end Wu2008DoubleSieve
