import MathlibNt.Wu2008DoubleSieve.PhiBounded
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Actual admissible improvements

Wu (2004), (3.1)--(3.4), uses the strict unscaled `P(d*N)` carrier.
The finite-threshold constraints below omit only `N < 4`; this leaves their
eventual union unchanged and avoids the zero logarithmic integral at two.
Increasing the threshold removes constraints, so the admissible sets increase.
This corrects the monotonicity direction printed immediately after (3.4).
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

def wuSourceBox (k : ℕ) (δ : ℝ) (N i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) : Prop :=
  i ≤ k ∧
  1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ ∧
  Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) ∧
  Antitone V ∧
  (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) ∧
  boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V

noncomputable def wuUpperCoefficient (s : ℝ) : ℝ :=
  s * jr1965F s / (2 * exp eulerMascheroniConstant)

noncomputable def wuLowerCoefficient (s : ℝ) : ℝ :=
  s * jr1965f s / (2 * exp eulerMascheroniConstant)

def wuImprovementComparison {i : ℕ} (upper : Bool) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s h : ℝ) : Prop :=
  if upper then
    wuBoxPhi N δ W s ≤ (wuUpperCoefficient s - h) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W
  else
    (wuLowerCoefficient s + h) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W ≤
      wuBoxPhi N δ W s

def wuAdmissibleImprovements (upper : Bool) (k : ℕ) (δ s : ℝ) (N0 : ℕ) : Set ℝ :=
  {h | ∀ N : ℕ, N0 ≤ N → 4 ≤ N → Even N →
    ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      wuImprovementComparison upper N δ (convolutionWuWindows N Δ V) s h}

def wuEventualImprovements (upper : Bool) (k : ℕ) (δ s : ℝ) : Set ℝ :=
  {h | ∃ N0 : ℕ, h ∈ wuAdmissibleImprovements upper k δ s N0}

theorem wuSourceBox_mono_depth {k l N i : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hkl : k ≤ l) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N)
    (hbox : wuSourceBox k δ N i Δ V) :
    wuSourceBox l δ N i Δ V := by
  refine ⟨hbox.1.trans hkl, hbox.2.1, hbox.2.2.1, hbox.2.2.2.1, ?_,
    hbox.2.2.2.2.2⟩
  intro j
  have hp : δ ^ (l + 1) ≤ δ ^ (k + 1) :=
    pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hp).trans
    (hbox.2.2.2.2.1 j)

theorem wuSourceBox_zero_depth (k N : ℕ) (δ : ℝ) (hN : 4 ≤ N) :
    wuSourceBox k δ N 0 (1 + log (N : ℝ) ^ (-4 : ℝ)) Fin.elim0 := by
  have hp : 0 < log (N : ℝ) ^ (-4 : ℝ) :=
    rpow_pos_of_pos (log_pos (by exact_mod_cast (show 1 < N by omega))) _
  refine ⟨Nat.zero_le _, le_rfl, by linarith, ?_, ?_, ?_⟩
  · intro a
    exact Fin.elim0 a
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j

theorem wuAdmissibleImprovements_mono_threshold (upper : Bool) (k : ℕ) (δ s : ℝ) :
    Monotone (wuAdmissibleImprovements upper k δ s) := by
  intro M N hMN h hh n hn
  exact hh n (hMN.trans hn)

theorem wuAdmissibleImprovements_antitone_depth (upper : Bool) {δ s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N0 : ℕ) :
    Antitone (fun k => wuAdmissibleImprovements upper k δ s N0) := by
  intro k l hkl h hh N hN hN4 he i Δ V hbox
  exact hh N hN hN4 he i Δ V
    (wuSourceBox_mono_depth hkl hδ hδ1 (by omega) hbox)

theorem wuEventualImprovements_antitone_depth (upper : Bool) {δ s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Antitone (fun k => wuEventualImprovements upper k δ s) := by
  intro k l hkl h ⟨N0, hh⟩
  exact ⟨N0, wuAdmissibleImprovements_antitone_depth upper hδ hδ1 N0 hkl hh⟩

/-- A real nonempty baseline is produced from the actual Phi estimates,
not assumed as a property of a named comparison family. -/
theorem wuEventualImprovements_neg_mem (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) (hε : 0 < ε) :
    -ε ∈ wuEventualImprovements upper k δ s := by
  cases upper
  · obtain ⟨N0, hN0⟩ := wu_boxPhi_lower_source_bounded k hk hδ hδhi hε
    refine ⟨N0, ?_⟩
    intro N hN _hN4 he i Δ V hbox
    simpa [wuImprovementComparison, wuLowerCoefficient, sub_eq_add_neg] using
      (hN0 N hN he i hbox.1 Δ hbox.2.1 hbox.2.2.1 V hbox.2.2.2.1
        hbox.2.2.2.2.1 hbox.2.2.2.2.2 s hs hs10).2
  · obtain ⟨N0, hN0⟩ := wu_boxPhi_upper_source_bounded k hk hδ hδhi hε
    refine ⟨N0, ?_⟩
    intro N hN _hN4 he i Δ V hbox
    simpa [wuImprovementComparison, wuUpperCoefficient] using
      (hN0 N hN he i hbox.1 Δ hbox.2.1 hbox.2.2.1 V hbox.2.2.2.1
        hbox.2.2.2.2.1 hbox.2.2.2.2.2 s hs hs10).1

theorem wu_zero_depth_theta_pos {N : ℕ} {δ : ℝ}
    (hN : 4 ≤ N) (hδhi : δ < 1 / 2) (W : Fin 0 → Finset ℕ) :
    0 < boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  rw [boxTheta_zero_depth]
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < log (N : ℝ) := log_pos hNr
  have hli : 0 < logarithmicIntegral N :=
    (by positivity : (0 : ℝ) < N / (2 * log N)).trans_le (box_trueLi_lower hN)
  have hC := wuSingularSeries_pos N (by omega)
  have hlog : 0 < log ((N : ℝ) ^ (1 / 2 - δ)) :=
    log_pos (one_lt_rpow hNr (by linarith))
  positivity

/-- Depth zero supplies an actual positive-mass test sequence, at arbitrarily
large even N; no abstract nonzero-Theta witness is postulated. -/
theorem wuEventualImprovements_upper_le {k : ℕ} {δ s h : ℝ}
    (hδhi : δ < 1 / 2) (hh : h ∈ wuEventualImprovements true k δ s) :
    h ≤ wuUpperCoefficient s := by
  obtain ⟨N0, hN0⟩ := hh
  let N := 2 * max 4 N0
  have hN4 : 4 ≤ N := by dsimp [N]; omega
  have hNN0 : N0 ≤ N := by dsimp [N]; omega
  have he : Even N := ⟨max 4 N0, by dsimp [N]; omega⟩
  let Δ := 1 + log (N : ℝ) ^ (-4 : ℝ)
  let W := convolutionWuWindows N Δ (Fin.elim0 : Fin 0 → ℝ)
  have hcmp := hN0 N hNN0 hN4 he 0 Δ Fin.elim0
    (wuSourceBox_zero_depth k N δ hN4)
  have hT := wu_zero_depth_theta_pos hN4 hδhi W
  have hP := wuBoxPhi_nonneg N δ W s
  change wuBoxPhi N δ W s ≤ (wuUpperCoefficient s - h) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W at hcmp
  have := nonneg_of_mul_nonneg_left (hP.trans hcmp) hT
  linarith

/-- The upper baseline on the unit convolution uniformly bounds every
eventual lower improvement, independently of its claimed depth. -/
theorem wuEventualImprovements_lower_le {k : ℕ} {δ s h : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hh : h ∈ wuEventualImprovements false k δ s) :
    h ≤ wuUpperCoefficient s - wuLowerCoefficient s := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N0, hN0⟩ := hh
  obtain ⟨M, hM⟩ := wu_boxPhi_upper_source_bounded 1 le_rfl hδ hδhi hε
  let N := 2 * max 4 (max N0 M)
  have hN4 : 4 ≤ N := by dsimp [N]; omega
  have hNN0 : N0 ≤ N := by dsimp [N]; omega
  have hNM : M ≤ N := by dsimp [N]; omega
  have he : Even N := ⟨max 4 (max N0 M), by dsimp [N]; omega⟩
  let Δ := 1 + log (N : ℝ) ^ (-4 : ℝ)
  let V : Fin 0 → ℝ := Fin.elim0
  let W := convolutionWuWindows N Δ V
  have hb := wuSourceBox_zero_depth k N δ hN4
  have hcmp := hN0 N hNN0 hN4 he 0 Δ V hb
  have hb1 := wuSourceBox_zero_depth 1 N δ hN4
  have hup := (hM N hNM he 0 (by omega) Δ hb1.2.1 hb1.2.2.1 V
    hb1.2.2.2.1 hb1.2.2.2.2.1 hb1.2.2.2.2.2 s hs hs10).1
  have hT := wu_zero_depth_theta_pos hN4 hδhi W
  change (wuLowerCoefficient s + h) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W ≤
    wuBoxPhi N δ W s at hcmp
  change wuBoxPhi N δ W s ≤ (wuUpperCoefficient s + ε) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W at hup
  have := (mul_le_mul_iff_left₀ hT).mp (hcmp.trans hup)
  linarith

theorem wuEventualImprovements_bddAbove (upper : Bool) (k : ℕ) {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    BddAbove (wuEventualImprovements upper k δ s) := by
  cases upper
  · exact ⟨wuUpperCoefficient s - wuLowerCoefficient s,
      fun _ hh => wuEventualImprovements_lower_le hδ hδhi hs hs10 hh⟩
  · exact ⟨wuUpperCoefficient s, fun _ hh => wuEventualImprovements_upper_le hδhi hh⟩

end Wu2008DoubleSieve
