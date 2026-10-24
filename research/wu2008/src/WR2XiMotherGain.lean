import WR2XiOriginalFeedback
import MathlibNt.Wu2008DoubleSieve.MotherPairFullFeedbackIntegrals

/-! Identify the original second-functional integrals with the actual mother gains. -/
noncomputable section
namespace WuPaper.R2Xi
open Wu2008DoubleSieve MotherPair

 theorem original66_eq_full_gain (p : SecondFunctionalParameters) (δ : ℝ) :
    original66 (wuImprovementLimit true δ) p = gamma5FullGain p δ :=
  (gamma5_full_gain_original_integral p δ).symm

 theorem original67_eq_gain {p : SecondFunctionalParameters} (hp : FullHParameters p) (δ : ℝ) :
    original67 (wuImprovementLimit true δ) p = gainIntegral p .gammaSix δ :=
  (fullH_gammaSix_original_integral hp δ).symm

 theorem original68_eq_gain_sum {p : SecondFunctionalParameters} (hp : FullHParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    original68 (wuImprovementLimit true δ) p =
      gainIntegral p .gammaSeven δ + gainIntegral p .gammaEight δ :=
  (fullH_gammaSevenEight_original_integral hp hδ hδhi).symm

/-- Only Gamma5 uses the full gain; the remaining original integrals are exact. -/
theorem originalSecondFeedback_eq_mother_gains {p : SecondFunctionalParameters}
    (hp : FullHParameters p) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    originalSecondFeedback δ p =
      (actualLowerJ δ p.s p.S + actualLowerJ δ p.kappa2 p.S + actualLowerJ δ p.kappa3 p.S +
        4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
        gamma5FullGain p δ + gainIntegral p .gammaSix δ +
        gainIntegral p .gammaSeven δ + gainIntegral p .gammaEight δ) / 5 := by
  unfold originalSecondFeedback
  rw [original66_eq_full_gain, original67_eq_gain hp, original68_eq_gain_sum hp hδ hδhi]
  ring

end WuPaper.R2Xi
