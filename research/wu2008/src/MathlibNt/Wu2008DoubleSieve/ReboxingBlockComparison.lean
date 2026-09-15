import MathlibNt.Wu2008DoubleSieve.ReboxingNormalization
import MathlibNt.Wu2008DoubleSieve.ImprovementThresholdIntegrals

/-!
# Actual finite-threshold comparison on an inserted prime block

Wu04 after (3.15): the constructed sorting permits use of the genuine
depth k+1 improvement on each inserted prime window. The threshold is
chosen before the coefficient parameter, N0, and every old source box.
This is a block estimate, not a payment for changing its cutoff to p.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

/-- Actual source comparisons at the increased depth, with all structural
membership discharged by sorted insertion. -/
theorem wu_reboxed_block_comparison (upper : Bool) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t α : ℝ, 2 ≤ s → 0 < t → t ≤ 10 →
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t) ≤ α →
        α ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) →
      ∀ u : ℝ, 1 ≤ u → u ≤ 10 →
        wuImprovementComparison upper N δ
          (Fin.cons (primeWindow N (α / Δ) α) (convolutionWuWindows N Δ V))
          u (wuImprovementAt upper (k + 1) δ u N0) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (wuImprovementAt_uniform_eventually_attained upper (k + 1) (by omega) hδ
      (show δ < 1 / 2 by linarith))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t α hs ht ht10 hαlo hαhi u hu hu10
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  obtain ⟨e, hbox⟩ := wuSourceBox_sorted_insertion (show 2 ≤ N by omega)
    hδ hδhi hb hs ht ht10 hαlo hαhi
  have hgain := (hT N0 ((le_max_right _ _).trans hN0) u hu hu10).2.1
  have hcmp := hgain N hN hN4 he (i + 1) Δ (Fin.cons α V ∘ e) hbox
  rw [convolutionWuWindows_permute, convolutionWuWindows_cons] at hcmp
  unfold wuImprovementComparison at hcmp ⊢
  rw [wuBoxPhi_permute, boxTheta_permute] at hcmp
  exact hcmp

/-- Both signed estimates are available at one common threshold for
the literal inserted convolution; no factor family is postulated. -/
theorem wu_reboxed_block_upper_lower (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t α : ℝ, 2 ≤ s → 0 < t → t ≤ 10 →
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t) ≤ α →
        α ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) →
      ∀ u : ℝ, 1 ≤ u → u ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let P := primeWindow N (α / Δ) α
        let S := ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ P, (sourceSieveCount N (d * p) ((d * p) * N)
            (wuLocalCutoff N δ (d * p) u) : ℝ)
        (wuLowerCoefficient u + wuImprovementAt false (k + 1) δ u N0) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (Fin.cons P W) ≤ S ∧
          S ≤ (wuUpperCoefficient u - wuImprovementAt true (k + 1) δ u N0) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (Fin.cons P W) := by
  obtain ⟨T1, hT1, hupper⟩ := wu_reboxed_block_comparison true k hδ hδhi
  obtain ⟨T2, _, hlower⟩ := wu_reboxed_block_comparison false k hδ hδhi
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t α hs ht ht10 hαlo hαhi u hu hu10
  have hu' := hupper N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t α hs ht ht10 hαlo hαhi u hu hu10
  have hl' := hlower N0 ((le_max_right _ _).trans hN0) N hN he
    i Δ V hb s t α hs ht ht10 hαlo hαhi u hu hu10
  simp only [wuImprovementComparison, Bool.false_eq_true, if_false, if_true,
    wuBoxPhi_cons] at hu' hl'
  exact ⟨hl', hu'⟩

end Wu2008DoubleSieve
