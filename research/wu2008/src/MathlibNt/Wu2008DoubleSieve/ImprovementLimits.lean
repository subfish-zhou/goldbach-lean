import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies

/-!
# The ordered improvement limits

Real suprema are used only after proving eventual nonemptiness and boundedness
for the actual Wu families. The inner limit is in the threshold `N0`, at fixed
depth and delta. The outer limit is in depth, with delta still fixed.
Nonnegativity is the linear-sieve baseline, not a positive double-sieve gain.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology

noncomputable def wuImprovementAt (upper : Bool) (k : ℕ) (δ s : ℝ) (N0 : ℕ) : ℝ :=
  sSup (wuAdmissibleImprovements upper k δ s N0)

noncomputable def wuImprovementAtInfinity (upper : Bool) (k : ℕ) (δ s : ℝ) : ℝ :=
  sSup (wuEventualImprovements upper k δ s)

noncomputable def wuImprovementLimit (upper : Bool) (δ s : ℝ) : ℝ :=
  ⨅ k : ℕ, wuImprovementAtInfinity upper (k + 1) δ s

theorem wuEventualImprovements_nonempty (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    (wuEventualImprovements upper k δ s).Nonempty :=
  ⟨-1, wuEventualImprovements_neg_mem upper k hk hδ hδhi hs hs10 (by norm_num)⟩

theorem wuImprovementAtInfinity_nonneg (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    0 ≤ wuImprovementAtInfinity upper k δ s := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := le_csSup (wuEventualImprovements_bddAbove upper k hδ hδhi hs hs10)
    (wuEventualImprovements_neg_mem upper k hk hδ hδhi hs hs10 hε)
  change -ε ≤ wuImprovementAtInfinity upper k δ s at h
  linarith

theorem wuImprovementAtInfinity_upper_bound {k : ℕ} (hk : 1 ≤ k) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    wuImprovementAtInfinity true k δ s ≤ wuUpperCoefficient s :=
  csSup_le (wuEventualImprovements_nonempty true k hk hδ hδhi hs hs10)
    (fun _ hh => wuEventualImprovements_upper_le hδhi hh)

theorem wuImprovementAtInfinity_lower_bound {k : ℕ} (hk : 1 ≤ k) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    wuImprovementAtInfinity false k δ s ≤ wuUpperCoefficient s - wuLowerCoefficient s :=
  csSup_le (wuEventualImprovements_nonempty false k hk hδ hδhi hs hs10)
    (fun _ hh => wuEventualImprovements_lower_le hδ hδhi hs hs10 hh)

/-- The base threshold supplies both a real member of the improvement set
and positive actual Theta for every remaining source box. -/
theorem wuImprovement_base_exists (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    ∃ T : ℕ, 4 ≤ T ∧ -1 ∈ wuAdmissibleImprovements upper k δ s T ∧
      ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
        wuSourceBox k δ N i Δ V →
        0 < boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨M, hM⟩ := wuEventualImprovements_neg_mem upper k hk hδ hδhi hs hs10
    (ε := 1) (by norm_num)
  obtain ⟨c, hc, L, hL⟩ := wu_boxTheta_lower k hδ hδhi
  refine ⟨max 4 (max M L), le_max_left _ _, ?_, ?_⟩
  · exact wuAdmissibleImprovements_mono_threshold upper k δ s
      ((le_max_left M L).trans (le_max_right _ _)) hM
  · intro N hN i Δ V hb
    have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
    have hNL : L ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    exact (by positivity : 0 < c * (N : ℝ) / log N ^ (5 * k + 2)).trans_le
      (hL N hNL i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.2.1 hb.2.2.2.2.2)

/-- After the positive-mass base threshold, the finite supremum itself
satisfies the actual source inequalities, as in Wu04 Lemma 3.2. -/
theorem wuImprovementAt_mem_of_positive_theta (upper : Bool) {k N0 : ℕ} {δ s : ℝ}
    (hne : (wuAdmissibleImprovements upper k δ s N0).Nonempty)
    (hθ : ∀ N : ℕ, N0 ≤ N → 4 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        0 < boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) :
    wuImprovementAt upper k δ s N0 ∈ wuAdmissibleImprovements upper k δ s N0 := by
  intro N hN hN4 he i Δ V hb
  have hT := hθ N hN hN4 he i Δ V hb
  cases upper
  · have hbound : wuImprovementAt false k δ s N0 ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s /
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) -
          wuLowerCoefficient s := by
      apply csSup_le hne
      intro h hh
      have hc := hh N hN hN4 he i Δ V hb
      change (wuLowerCoefficient s + h) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _ at hc
      have := (le_div_iff₀ hT).2 hc
      linarith
    change (wuLowerCoefficient s + wuImprovementAt false k δ s N0) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _
    apply (le_div_iff₀ hT).1
    linarith
  · have hbound : wuImprovementAt true k δ s N0 ≤
        wuUpperCoefficient s -
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s /
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
      apply csSup_le hne
      intro h hh
      have hc := hh N hN hN4 he i Δ V hb
      change _ ≤ (wuUpperCoefficient s - h) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) at hc
      have := (div_le_iff₀ hT).2 hc
      linarith
    change _ ≤ (wuUpperCoefficient s - wuImprovementAt true k δ s N0) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
    apply (div_le_iff₀ hT).1
    linarith

theorem wuImprovementAt_eventually_attained (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    ∀ᶠ N0 : ℕ in atTop,
      (wuAdmissibleImprovements upper k δ s N0).Nonempty ∧
      wuImprovementAt upper k δ s N0 ∈ wuAdmissibleImprovements upper k δ s N0 := by
  obtain ⟨T, _, hT, hθ⟩ := wuImprovement_base_exists upper k hk hδ hδhi hs hs10
  filter_upwards [eventually_ge_atTop T] with N0 hN0
  have hne : (wuAdmissibleImprovements upper k δ s N0).Nonempty :=
    ⟨-1, wuAdmissibleImprovements_mono_threshold upper k δ s hN0 hT⟩
  exact ⟨hne, wuImprovementAt_mem_of_positive_theta upper hne
    (fun N hN _ _ i Δ V hb => hθ N (hN0.trans hN) i Δ V hb)⟩

/-- The first, fixed-depth limit is the supremum of the eventual
improvements. Only a fixed initial segment of N0 is discarded. -/
theorem wuImprovementAt_tendsto (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    Tendsto (wuImprovementAt upper k δ s) atTop
      (𝓝 (wuImprovementAtInfinity upper k δ s)) := by
  obtain ⟨T, _, hT, _⟩ := wuImprovement_base_exists upper k hk hδ hδhi hs hs10
  have hne : ∀ n : ℕ, (wuAdmissibleImprovements upper k δ s (max T n)).Nonempty :=
    fun n => ⟨-1, wuAdmissibleImprovements_mono_threshold upper k δ s
      (le_max_left _ _) hT⟩
  have hE := wuEventualImprovements_bddAbove upper k hδ hδhi hs hs10
  have hsub : ∀ n : ℕ, wuAdmissibleImprovements upper k δ s n ⊆
      wuEventualImprovements upper k δ s :=
    fun n _ hh => ⟨n, hh⟩
  have hmono : Monotone (fun n => wuImprovementAt upper k δ s (max T n)) := by
    intro m n hmn
    exact csSup_le_csSup (hE.mono (hsub _)) (hne m)
      (wuAdmissibleImprovements_mono_threshold upper k δ s (max_le_max_left T hmn))
  have hlub : IsLUB (Set.range (fun n => wuImprovementAt upper k δ s (max T n)))
      (wuImprovementAtInfinity upper k δ s) := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact csSup_le_csSup hE (hne n) (hsub _)
    · intro b hb
      apply csSup_le (wuEventualImprovements_nonempty upper k hk hδ hδhi hs hs10)
      intro h ⟨n, hn⟩
      have hmem := wuAdmissibleImprovements_mono_threshold upper k δ s
        (le_max_right T n) hn
      exact (le_csSup (hE.mono (hsub _)) hmem).trans (hb ⟨n, rfl⟩)
  have ht := tendsto_atTop_isLUB hmono hlub
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with n hn
  rw [max_eq_right hn]

/-- The printed threshold monotonicity has the opposite direction:
the real suprema are nondecreasing once nonemptiness is established. -/
theorem wuImprovementAt_eventually_monotone (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    ∃ T : ℕ, MonotoneOn (wuImprovementAt upper k δ s) (Ici T) := by
  obtain ⟨T, _, hT, _⟩ := wuImprovement_base_exists upper k hk hδ hδhi hs hs10
  refine ⟨T, ?_⟩
  intro m hm n _ hmn
  have hE := wuEventualImprovements_bddAbove upper k hδ hδhi hs hs10
  have hsub : wuAdmissibleImprovements upper k δ s n ⊆
      wuEventualImprovements upper k δ s := fun _ hh => ⟨n, hh⟩
  apply csSup_le_csSup (hE.mono hsub)
    ⟨-1, wuAdmissibleImprovements_mono_threshold upper k δ s hm hT⟩
  exact wuAdmissibleImprovements_mono_threshold upper k δ s hmn

theorem wuImprovementAtInfinity_antitone (upper : Bool) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    Antitone (fun k : ℕ => wuImprovementAtInfinity upper (k + 1) δ s) := by
  intro k l hkl
  exact csSup_le_csSup (wuEventualImprovements_bddAbove upper (k + 1) hδ hδhi hs hs10)
    (wuEventualImprovements_nonempty upper (l + 1) (by omega) hδ hδhi hs hs10)
    (wuEventualImprovements_antitone_depth upper hδ (by linarith) (by omega))

/-- Only after the fixed-depth threshold limit do we take the depth limit.
There is no threshold asserted uniformly for a growing depth. -/
theorem wuImprovementAtInfinity_tendsto (upper : Bool) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    Tendsto (fun k : ℕ => wuImprovementAtInfinity upper (k + 1) δ s) atTop
      (𝓝 (wuImprovementLimit upper δ s)) := by
  apply tendsto_atTop_ciInf (wuImprovementAtInfinity_antitone upper hδ hδhi hs hs10)
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact wuImprovementAtInfinity_nonneg upper (k + 1) (by omega) hδ hδhi hs hs10

theorem wuImprovementLimit_nonneg (upper : Bool) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    0 ≤ wuImprovementLimit upper δ s := by
  exact le_ciInf (fun k => wuImprovementAtInfinity_nonneg upper (k + 1)
    (by omega) hδ hδhi hs hs10)

theorem wuImprovementLimit_le_fixed_depth (upper : Bool) (k : ℕ) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    wuImprovementLimit upper δ s ≤ wuImprovementAtInfinity upper (k + 1) δ s := by
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro _ ⟨l, rfl⟩
  exact wuImprovementAtInfinity_nonneg upper (l + 1) (by omega) hδ hδhi hs hs10

theorem wuImprovementComparison_mono {i N : ℕ} {δ s h h' : ℝ}
    {W : Fin i → Finset ℕ} (upper : Bool)
    (hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W)
    (hle : h ≤ h') (hc : wuImprovementComparison upper N δ W s h') :
    wuImprovementComparison upper N δ W s h := by
  cases upper <;> simp only [wuImprovementComparison, Bool.false_eq_true,
    if_false, if_true] at hc ⊢ <;>
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) hθ]

/-- The admissible eventual sets are genuine lower sets. Positivity is
obtained from the actual box-mass producer before weakening a coefficient. -/
theorem wuEventualImprovements_downward (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s h h' : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hle : h ≤ h') (hh : h' ∈ wuEventualImprovements upper k δ s) :
    h ∈ wuEventualImprovements upper k δ s := by
  obtain ⟨M, hM⟩ := hh
  obtain ⟨T, _, _, hθ⟩ := wuImprovement_base_exists upper k hk hδ hδhi hs hs10
  refine ⟨max M T, ?_⟩
  intro N hN hN4 he i Δ V hb
  exact wuImprovementComparison_mono upper
    (hθ N ((le_max_right _ _).trans hN) i Δ V hb).le hle
    (hM N ((le_max_left _ _).trans hN) hN4 he i Δ V hb)

/-- A strict amount below the limiting improvement is available uniformly
on every fixed-depth family. The epsilon cannot be removed from this claim. -/
theorem wuImprovementLimit_sub_mem (upper : Bool) (k : ℕ) {δ s ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) (hε : 0 < ε) :
    wuImprovementLimit upper δ s - ε ∈ wuEventualImprovements upper (k + 1) δ s := by
  have hlt : wuImprovementLimit upper δ s - ε <
      sSup (wuEventualImprovements upper (k + 1) δ s) :=
    (sub_lt_self _ hε).trans_le
      (wuImprovementLimit_le_fixed_depth upper k hδ hδhi hs hs10)
  obtain ⟨h, hh, hgt⟩ := exists_lt_of_lt_csSup
    (wuEventualImprovements_nonempty upper (k + 1) (by omega) hδ hδhi hs hs10) hlt
  exact wuEventualImprovements_downward upper (k + 1) (by omega)
    hδ hδhi hs hs10 hgt.le hh

/-- Both limiting functions are real and bounded; these are upper bounds
on possible gains, not positive lower bounds. -/
theorem wuImprovementLimit_bounds {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    0 ≤ wuImprovementLimit true δ s ∧
      wuImprovementLimit true δ s ≤ wuUpperCoefficient s ∧
      0 ≤ wuImprovementLimit false δ s ∧
      wuImprovementLimit false δ s ≤ wuUpperCoefficient s - wuLowerCoefficient s := by
  exact ⟨wuImprovementLimit_nonneg true hδ hδhi hs hs10,
    (wuImprovementLimit_le_fixed_depth true 0 hδ hδhi hs hs10).trans
      (wuImprovementAtInfinity_upper_bound le_rfl hδ hδhi hs hs10),
    wuImprovementLimit_nonneg false hδ hδhi hs hs10,
    (wuImprovementLimit_le_fixed_depth false 0 hδ hδhi hs hs10).trans
      (wuImprovementAtInfinity_lower_bound le_rfl hδ hδhi hs hs10)⟩

end Wu2008DoubleSieve
