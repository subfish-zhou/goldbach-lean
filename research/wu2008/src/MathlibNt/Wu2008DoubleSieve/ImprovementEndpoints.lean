import MathlibNt.Wu2008DoubleSieve.ImprovementLimits

/-!
# Strict and closed limiting improvements

Wu04 uses strict sifting while Wu08 prints closed sifting. Their finite
threshold suprema need not agree. The proved relative endpoint estimate
does identify the eventual suprema, and hence the ordered limiting gains.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology

def wuClosedImprovementComparison {i : ℕ} (upper : Bool) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s h : ℝ) : Prop :=
  if upper then
    wuBoxPhiLE N δ W s ≤ (wuUpperCoefficient s - h) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W
  else
    (wuLowerCoefficient s + h) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W ≤
      wuBoxPhiLE N δ W s

def wuClosedAdmissibleImprovements (upper : Bool) (k : ℕ) (δ s : ℝ) (N0 : ℕ) :
    Set ℝ :=
  {h | ∀ N : ℕ, N0 ≤ N → 4 ≤ N → Even N →
    ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      wuClosedImprovementComparison upper N δ (convolutionWuWindows N Δ V) s h}

def wuClosedEventualImprovements (upper : Bool) (k : ℕ) (δ s : ℝ) : Set ℝ :=
  {h | ∃ N0 : ℕ, h ∈ wuClosedAdmissibleImprovements upper k δ s N0}

noncomputable def wuClosedImprovementAt (upper : Bool) (k : ℕ) (δ s : ℝ) (N0 : ℕ) : ℝ :=
  sSup (wuClosedAdmissibleImprovements upper k δ s N0)

noncomputable def wuClosedImprovementAtInfinity (upper : Bool) (k : ℕ) (δ s : ℝ) : ℝ :=
  sSup (wuClosedEventualImprovements upper k δ s)

noncomputable def wuClosedImprovementLimit (upper : Bool) (δ s : ℝ) : ℝ :=
  ⨅ k : ℕ, wuClosedImprovementAtInfinity upper (k + 1) δ s

/-- Uniform epsilon-transfer in both directions, retaining the actual
endpoint sum rather than asserting equality of the two finite carriers. -/
theorem wu_improvement_endpoint_transfer (upper : Bool) (k : ℕ) {δ s ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ h : ℝ,
        (wuImprovementComparison upper N δ (convolutionWuWindows N Δ V) s h →
          wuClosedImprovementComparison upper N δ (convolutionWuWindows N Δ V) s (h - ε)) ∧
        (wuClosedImprovementComparison upper N δ (convolutionWuWindows N Δ V) s h →
          wuImprovementComparison upper N δ (convolutionWuWindows N Δ V) s (h - ε)) := by
  obtain ⟨T, hT⟩ := wu_boxPhi_endpoint_relative k hδ hδhi hε
  refine ⟨T, ?_⟩
  intro N hN he i Δ V hb h
  have hE := hT N hN he i hb.1 Δ hb.2.1 hb.2.2.1 V hb.2.2.2.2.1
    hb.2.2.2.2.2 s hs hs10
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right (hE.1.trans hE.2) hε
  cases upper <;> simp only [wuImprovementComparison, wuClosedImprovementComparison,
    Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> intro hc <;> nlinarith [mul_nonneg hε.le hθ]

theorem wuEventualImprovements_to_closed (upper : Bool) (k : ℕ) {δ s h ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hε : 0 < ε) (hh : h ∈ wuEventualImprovements upper k δ s) :
    h - ε ∈ wuClosedEventualImprovements upper k δ s := by
  obtain ⟨M, hM⟩ := hh
  obtain ⟨T, hT⟩ := wu_improvement_endpoint_transfer upper k hδ hδhi hs hs10 hε
  refine ⟨max M T, ?_⟩
  intro N hN hN4 he i Δ V hb
  exact (hT N ((le_max_right _ _).trans hN) he i Δ V hb h).1
    (hM N ((le_max_left _ _).trans hN) hN4 he i Δ V hb)

theorem wuClosedEventualImprovements_to_strict (upper : Bool) (k : ℕ) {δ s h ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hε : 0 < ε) (hh : h ∈ wuClosedEventualImprovements upper k δ s) :
    h - ε ∈ wuEventualImprovements upper k δ s := by
  obtain ⟨M, hM⟩ := hh
  obtain ⟨T, hT⟩ := wu_improvement_endpoint_transfer upper k hδ hδhi hs hs10 hε
  refine ⟨max M T, ?_⟩
  intro N hN hN4 he i Δ V hb
  exact (hT N ((le_max_right _ _).trans hN) he i Δ V hb h).2
    (hM N ((le_max_left _ _).trans hN) hN4 he i Δ V hb)

theorem wuClosedEventualImprovements_nonempty (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    (wuClosedEventualImprovements upper k δ s).Nonempty := by
  refine ⟨-1 - 1, ?_⟩
  exact wuEventualImprovements_to_closed upper k hδ hδhi hs (by linarith) (by norm_num)
    (wuEventualImprovements_neg_mem upper k hk hδ hδhi hs hs10 (by norm_num))

theorem wuClosedEventualImprovements_le_strict_sup (upper : Bool) (k : ℕ)
    {δ s h : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hh : h ∈ wuClosedEventualImprovements upper k δ s) :
    h ≤ wuImprovementAtInfinity upper k δ s := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hmem := wuClosedEventualImprovements_to_strict upper k hδ hδhi hs
    (by linarith) hε hh
  have hbound := le_csSup (wuEventualImprovements_bddAbove upper k hδ hδhi hs hs10) hmem
  change h - ε ≤ wuImprovementAtInfinity upper k δ s at hbound
  linarith

theorem wuClosedEventualImprovements_bddAbove (upper : Bool) (k : ℕ)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    BddAbove (wuClosedEventualImprovements upper k δ s) :=
  ⟨wuImprovementAtInfinity upper k δ s,
    fun _ hh => wuClosedEventualImprovements_le_strict_sup upper k hδ hδhi hs hs10 hh⟩

/-- Strict and closed sifting give the same fixed-depth eventual supremum,
although the finite-threshold quantities have not been identified. -/
theorem wuClosedImprovementAtInfinity_eq (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    wuClosedImprovementAtInfinity upper k δ s = wuImprovementAtInfinity upper k δ s := by
  apply le_antisymm
  · exact csSup_le (wuClosedEventualImprovements_nonempty upper k hk hδ hδhi hs hs10)
      (fun _ hh => wuClosedEventualImprovements_le_strict_sup upper k hδ hδhi hs hs10 hh)
  · apply csSup_le (wuEventualImprovements_nonempty upper k hk hδ hδhi hs hs10)
    intro h hh
    apply le_of_forall_pos_le_add
    intro ε hε
    have hmem := wuEventualImprovements_to_closed upper k hδ hδhi hs
      (by linarith) hε hh
    have hbound := le_csSup
      (wuClosedEventualImprovements_bddAbove upper k hδ hδhi hs hs10) hmem
    change h - ε ≤ wuClosedImprovementAtInfinity upper k δ s at hbound
    linarith



theorem wuClosedAdmissibleImprovements_mono_threshold (upper : Bool) (k : ℕ) (δ s : ℝ) :
    Monotone (wuClosedAdmissibleImprovements upper k δ s) := by
  intro M N hMN h hh n hn
  exact hh n (hMN.trans hn)



end Wu2008DoubleSieve
