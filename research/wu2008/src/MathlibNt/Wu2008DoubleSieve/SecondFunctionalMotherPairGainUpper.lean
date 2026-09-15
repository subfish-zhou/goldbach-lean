import MathlibNt.Wu2008DoubleSieve.MotherPairGainSufficiency
import MathlibNt.Wu2008DoubleSieve.MotherPairGainFamily

namespace Wu2008DoubleSieve.MotherPair
open Finset Real
open scoped Classical

/-- The actual finite sufficient family is chosen before the uniform source threshold. -/
theorem original_gain_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ V, wuSourceBox k δ N i Δ V →
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
          (classicalIntegral p j - gainIntegral p j δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1/2 := by linarith
  obtain ⟨F,hF,hgain⟩ := sufficient_family hp j hδ hδhalf (half_pos hε)
  obtain ⟨T,hT,hcount⟩ := fixed_family_original_upper p hp j F hF k hk hδ hδhi (half_pos hε)
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb
  have hθ := gamma5Mass_theta_nonneg (by omega : 2 ≤ N) hδ hδhalf hb
  apply (hcount N hN he i Δ V hb).trans
  apply mul_le_mul_of_nonneg_right _ hθ
  linarith only [hgain]

/-- One common threshold covers all four original terms. -/
theorem original_gain_upper_uniform (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ V, wuSourceBox k δ N i Δ V → ∀ j : Term,
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
          (classicalIntegral p j - gainIntegral p j δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  choose T hT h using (fun j : Term => original_gain_upper p hp j k hk hδ hδhi hε)
  refine ⟨univ.sup T,(hT .gammaFive).trans (le_sup (mem_univ _)),?_⟩
  intro N hN he i Δ V hb j
  exact h j N ((le_sup (mem_univ j)).trans hN) he i Δ V hb

/-- Literal sum of the four classical integrals minus their actual legal H integrals. -/
noncomputable def fourIntegralUpper (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  (classicalIntegral p .gammaFive - gainIntegral p .gammaFive δ) +
  (classicalIntegral p .gammaSix - gainIntegral p .gammaSix δ) +
  (classicalIntegral p .gammaSeven - gainIntegral p .gammaSeven δ) +
  (classicalIntegral p .gammaEight - gainIntegral p .gammaEight δ)

theorem original_four_gain_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ V, wuSourceBox k δ N i Δ V →
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 +
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 6 +
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 7 +
        secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 8 ≤
          (fourIntegralUpper p δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,h⟩ := original_gain_upper_uniform p hp k hk hδ hδhi (show 0 < ε/4 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb
  have h5 := h N hN he i Δ V hb .gammaFive
  have h6 := h N hN he i Δ V hb .gammaSix
  have h7 := h N hN he i Δ V hb .gammaSeven
  have h8 := h N hN he i Δ V hb .gammaEight
  simp only [Term.index] at h5 h6 h7 h8
  unfold fourIntegralUpper
  linarith only [h5,h6,h7,h8]

end Wu2008DoubleSieve.MotherPair
