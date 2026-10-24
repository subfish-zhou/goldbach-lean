import MathlibNt.Wu2008DoubleSieve.MotherPairGamma5LossBudget
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairGainUpper

/-! Paid full-triangle Γ₅ bounds for the actual mother count in all four rows. -/
namespace Wu2008DoubleSieve.MotherPair
open Real
open Wu2004MeanValue.GammaFiveLossBudget

/-- The original counted Γ₅ term admits the full gain with the explicit row debit.
All source labels and convolution weights in the existing count are retained. -/
theorem gamma5_original_row_count_upper_paid (r : Fin 4) (k : ℕ) (hk : 1 ≤ k)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ V, wuSourceBox k δ N i Δ V →
        secondFunctionalMotherGammaSum (gamma5OriginalRow r) N δ
          (convolutionWuWindows N Δ V) 5 ≤
          (classicalIntegral (gamma5OriginalRow r) .gammaFive -
            gamma5FullGain (gamma5OriginalRow r) δ + 5*rowDebit r/2 + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hp : AnalyticParameters (gamma5OriginalRow r) := by
    fin_cases r
    · exact row1_fullH.toAnalyticParameters
    · exact row2_fullH.toAnalyticParameters
    · exact row3_fullH.toAnalyticParameters
    · exact row4_fullH.toAnalyticParameters
  obtain ⟨T,hT,hcount⟩ := original_gain_upper (gamma5OriginalRow r) hp .gammaFive k hk hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb
  have hhalf : δ < 1/2 := by linarith
  have hθ := gamma5Mass_theta_nonneg (show 2 ≤ N by omega) hδ hhalf hb
  have hloss := gamma5_original_row_full_sub_legal_lt r hδ hhalf
  exact (hcount N hN he i Δ V hb).trans
    (mul_le_mul_of_nonneg_right (by linarith) hθ)

end Wu2008DoubleSieve.MotherPair
