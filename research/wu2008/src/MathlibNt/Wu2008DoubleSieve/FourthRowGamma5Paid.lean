import MathlibNt.Wu2008DoubleSieve.FourthRowGamma5LinkMain
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackLossBudget

/-!
# Full Gamma₅ gain with an explicit debit in the fourth-row mother

The original fivefold mother already admits the legal Gamma₅ gain. Replacing
that gain by the full triangle costs less than 1/400 of the box normalization.
All other mother terms stay literal. After division by five the debit is
1/2000; estimates for those remaining terms are still needed for Ξ₂.
-/

namespace Wu2008DoubleSieve

/-- The full-triangle gain enters the original mother with its proved debit. -/
theorem fourthRowGamma5Link_full_gain_paid (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (5/2) ≤
          fourthRowGamma5LinkRHSwithoutGamma5 N δ (convolutionWuWindows N Δ V) +
            (gamma5MassC5 - gamma5FeedbackFullGain δ + 1/400 + ε) *
              boxTheta N ((N : ℝ) ^ (1/2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, hcount⟩ := fourthRowGamma5Link_full_integral_upper k hk hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  have hdhalf : δ < 1/2 := by linarith
  have hΘ := gamma5Mass_theta_nonneg (show 2 ≤ N by omega) hδ hdhalf hb
  have hpaid := gamma5Feedback_full_gain_sub_legal_lt hδ hdhalf
  have hc := hcount N hN he i Δ V hb
  rw [← gamma5Feedback_legal_gain_eq hδ hdhalf] at hc
  apply hc.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hΘ
  linarith only [hpaid]

end Wu2008DoubleSieve
