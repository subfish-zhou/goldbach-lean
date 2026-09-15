import MathlibNt.Wu2008DoubleSieve.ImprovementEndpoints

/-!
# Monotonicity of the effective source coefficients

Wu04's proof of Proposition 2, between (3.15) and (3.16), uses that
`A(s) - H_{k,N0}(s)` increases with s. The actual finite carrier
monotonicity proves the corresponding eventual and limiting statements.
It also proves H decreasing on the initial upper branch and h increasing
on the zero lower branch; no integral double-sieve comparison is inferred.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem wuSourceBox_phi_mono {k N i : ℕ} {δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hN : 4 ≤ N)
    (hb : wuSourceBox k δ N i Δ V) (hs : 1 ≤ s) (hst : s ≤ t) :
    wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) t := by
  apply wuBoxPhi_mono_parameter _ _ (by linarith) hst
  intro d hd
  exact (wuVariableRosserLevel_geometry (by omega) hδ hδhi
    hb.2.2.2.2.1 hb.2.2.2.2.2 hd hs).2.1.le

theorem wuAdmissibleImprovements_upper_shift {k N0 : ℕ} {δ s t h : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t)
    (hh : h ∈ wuAdmissibleImprovements true k δ t N0) :
    h + wuUpperCoefficient s - wuUpperCoefficient t ∈
      wuAdmissibleImprovements true k δ s N0 := by
  intro N hN hN4 he i Δ V hb
  have hcmp := (wuSourceBox_phi_mono hδ hδhi hN4 hb hs hst).trans
    (hh N hN hN4 he i Δ V hb)
  change _ ≤ (wuUpperCoefficient t - h) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) at hcmp
  change _ ≤ (wuUpperCoefficient s -
    (h + wuUpperCoefficient s - wuUpperCoefficient t)) * _
  convert hcmp using 1
  ring

theorem wuAdmissibleImprovements_lower_shift {k N0 : ℕ} {δ s t h : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t)
    (hh : h ∈ wuAdmissibleImprovements false k δ s N0) :
    h + wuLowerCoefficient s - wuLowerCoefficient t ∈
      wuAdmissibleImprovements false k δ t N0 := by
  intro N hN hN4 he i Δ V hb
  have hcmp := (hh N hN hN4 he i Δ V hb).trans
    (wuSourceBox_phi_mono hδ hδhi hN4 hb hs hst)
  change (wuLowerCoefficient s + h) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _ at hcmp
  change (wuLowerCoefficient t +
    (h + wuLowerCoefficient s - wuLowerCoefficient t)) * _ ≤ _
  convert hcmp using 1
  ring

/-- The finite-threshold effective upper coefficient used in the source's
reboxing comparison, for each pair of parameters after a common threshold. -/
theorem wu_effective_upper_threshold_eventually_mono (k : ℕ) (hk : 1 ≤ k) {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10) :
    ∀ᶠ N0 : ℕ in atTop,
      wuUpperCoefficient s - wuImprovementAt true k δ s N0 ≤
        wuUpperCoefficient t - wuImprovementAt true k δ t N0 := by
  filter_upwards [wuImprovementAt_eventually_attained true k hk hδ hδhi
    (hs.trans hst) ht10] with N0 hN0
  have hEs := wuEventualImprovements_bddAbove true k hδ hδhi hs (hst.trans ht10)
  have hsub : wuAdmissibleImprovements true k δ s N0 ⊆ wuEventualImprovements true k δ s :=
    fun _ hh => ⟨N0, hh⟩
  have hmem := wuAdmissibleImprovements_upper_shift hδ hδhi hs hst hN0.2
  have hbound := le_csSup (hEs.mono hsub) hmem
  change _ ≤ wuImprovementAt true k δ s N0 at hbound
  linarith

theorem wu_effective_upper_fixed_depth_mono (k : ℕ) (hk : 1 ≤ k) {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10) :
    wuUpperCoefficient s - wuImprovementAtInfinity true k δ s ≤
      wuUpperCoefficient t - wuImprovementAtInfinity true k δ t := by
  have hsup : wuImprovementAtInfinity true k δ t ≤
      wuImprovementAtInfinity true k δ s + wuUpperCoefficient t - wuUpperCoefficient s := by
    apply csSup_le (wuEventualImprovements_nonempty true k hk hδ hδhi (hs.trans hst) ht10)
    intro h ⟨N0, hN0⟩
    have hm : h + wuUpperCoefficient s - wuUpperCoefficient t ∈
        wuEventualImprovements true k δ s :=
      ⟨N0, wuAdmissibleImprovements_upper_shift hδ hδhi hs hst hN0⟩
    have hbound := le_csSup
      (wuEventualImprovements_bddAbove true k hδ hδhi hs (hst.trans ht10)) hm
    change _ ≤ wuImprovementAtInfinity true k δ s at hbound
    linarith
  linarith

theorem wu_effective_lower_fixed_depth_mono (k : ℕ) (hk : 1 ≤ k) {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10) :
    wuLowerCoefficient s + wuImprovementAtInfinity false k δ s ≤
      wuLowerCoefficient t + wuImprovementAtInfinity false k δ t := by
  have hsup : wuImprovementAtInfinity false k δ s ≤
      wuImprovementAtInfinity false k δ t + wuLowerCoefficient t - wuLowerCoefficient s := by
    apply csSup_le (wuEventualImprovements_nonempty false k hk hδ hδhi hs (hst.trans ht10))
    intro h ⟨N0, hN0⟩
    have hm : h + wuLowerCoefficient s - wuLowerCoefficient t ∈
        wuEventualImprovements false k δ t :=
      ⟨N0, wuAdmissibleImprovements_lower_shift hδ hδhi hs hst hN0⟩
    have hbound := le_csSup
      (wuEventualImprovements_bddAbove false k hδ hδhi (hs.trans hst) ht10) hm
    change _ ≤ wuImprovementAtInfinity false k δ t at hbound
    linarith
  linarith

theorem wu_effective_upper_limit_mono {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10) :
    wuUpperCoefficient s - wuImprovementLimit true δ s ≤
      wuUpperCoefficient t - wuImprovementLimit true δ t := by
  apply le_of_tendsto_of_tendsto
    ((wuImprovementAtInfinity_tendsto true hδ hδhi hs (hst.trans ht10)).const_sub _)
    ((wuImprovementAtInfinity_tendsto true hδ hδhi (hs.trans hst) ht10).const_sub _)
  exact Eventually.of_forall (fun k => wu_effective_upper_fixed_depth_mono (k + 1)
    (by omega) hδ hδhi hs hst ht10)

theorem wu_effective_lower_limit_mono {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10) :
    wuLowerCoefficient s + wuImprovementLimit false δ s ≤
      wuLowerCoefficient t + wuImprovementLimit false δ t := by
  apply le_of_tendsto_of_tendsto
    ((wuImprovementAtInfinity_tendsto false hδ hδhi hs (hst.trans ht10)).const_add _)
    ((wuImprovementAtInfinity_tendsto false hδ hδhi (hs.trans hst) ht10).const_add _)
  exact Eventually.of_forall (fun k => wu_effective_lower_fixed_depth_mono (k + 1)
    (by omega) hδ hδhi hs hst ht10)

theorem wuImprovementLimit_upper_antitone_initial {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    AntitoneOn (wuImprovementLimit true δ) (Icc 1 3) := by
  intro s hs t ht hst
  have hm := wu_effective_upper_limit_mono hδ hδhi hs.1 hst (by linarith [ht.2])
  have hAs : wuUpperCoefficient s = 1 :=
    jr1965F_normalized_initial (by linarith [hs.1]) hs.2
  have hAt : wuUpperCoefficient t = 1 :=
    jr1965F_normalized_initial (by linarith [ht.1]) ht.2
  rw [hAs, hAt] at hm
  linarith

theorem wuImprovementLimit_lower_monotone_initial {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    MonotoneOn (wuImprovementLimit false δ) (Icc 1 2) := by
  intro s hs t ht hst
  have hm := wu_effective_lower_limit_mono hδ hδhi hs.1 hst (by linarith [ht.2])
  have has : wuLowerCoefficient s = 0 := by
    simp [wuLowerCoefficient, jr1965f_initial hs.2]
  have hat : wuLowerCoefficient t = 0 := by
    simp [wuLowerCoefficient, jr1965f_initial ht.2]
  simpa only [has, hat, zero_add] using hm

end Wu2008DoubleSieve
