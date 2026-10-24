import MathlibNt.Wu2008DoubleSieve.MotherPairGamma5LossBudget
import MathlibNt.Wu2008DoubleSieve.MotherPairGainBounds

namespace Wu2008DoubleSieve.MotherPair
open Set Real MeasureTheory
open scoped Interval

/-- Put the outer factor in the form used in the original double integrals. -/
private theorem integral_div_outer (f : ℝ → ℝ) (a b t : ℝ) :
    (∫ u in a..b, f u / (t*u*(1-t-u))) =
      (∫ u in a..b, f u / (u*(1-t-u))) / t := by
  rw [← intervalIntegral.integral_div]
  congr 1
  funext u
  rw [div_div]
  congr 1
  ring

theorem gamma5_full_gain_original_integral (p : SecondFunctionalParameters) (δ : ℝ) :
    gamma5FullGain p δ = ∫ t in (1/p.S)..(1/p.kappa2),
      (∫ u in t..(1/p.kappa2),
        wuImprovementLimit true δ (p.S-p.S*t-p.S*u)/(u*(1-t-u))) / t := by
  unfold gamma5FullGain
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [integral_div_outer]
  congr 1
  congr 1
  funext u
  congr 2
  ring

theorem fullH_gammaSix_original_integral {p : SecondFunctionalParameters}
    (h : FullHParameters p) (δ : ℝ) :
    gainIntegral p .gammaSix δ = ∫ t in (1/p.S)..(1/p.kappa1),
      (∫ u in (1/p.kappa2)..(1/p.kappa3),
        wuImprovementLimit true δ (p.S-p.S*t-p.S*u)/(u*(1-t-u))) / t := by
  rw [fullH_gammaSix_integral h]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [integral_div_outer]
  congr 1
  congr 1
  funext u
  congr 2
  ring

/-- The adjacent Gamma7 and Gamma8 domains form the original single triangle. -/
theorem fullH_gammaSevenEight_original_integral {p : SecondFunctionalParameters}
    (h : FullHParameters p) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral p .gammaSeven δ + gainIntegral p .gammaEight δ =
      ∫ t in (1/p.S)..(1/p.kappa1),
        (∫ u in t..(1/p.kappa2),
          wuImprovementLimit true δ ((1-t-u)/t)/(u*(1-t-u))) / t := by
  have ha := h.toAnalyticParameters
  obtain ⟨_,hab,hbc,hce,_,_⟩ := parameter_order ha
  have ho7 := gain_outer_integrable ha .gammaSeven hδ hδhi
  have ho8 := gain_outer_integrable ha .gammaEight hδ hδhi
  unfold gainIntegral
  simp only [upperP] at ho7 ho8 ⊢
  rw [← intervalIntegral.integral_add ho7 ho8]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab]
  intro t ht
  dsimp only
  have h7 := gain_inner_integrable ha .gammaSeven hδ hδhi ht
  have h8 := gain_inner_integrable ha .gammaEight hδ hδhi ht
  simp only [upperQ,lowerQ,max_eq_right ht.1,min_eq_right ht.2] at h7
  simp only [upperQ,lowerQ,max_eq_left ht.2,min_eq_right hbc.le] at h8
  simp only [upperQ,lowerQ,max_eq_right ht.1,min_eq_right ht.2,
    max_eq_left ht.2,min_eq_right hbc.le]
  change (∫ u in t..(1/p.kappa1), gainLiteral p .gammaSeven δ t u) +
    (∫ u in (1/p.kappa1)..(1/p.kappa2), gainLiteral p .gammaSeven δ t u) = _
  rw [intervalIntegral.integral_add_adjacent_intervals h7 h8, ← integral_div_outer]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (ht.2.trans hbc.le)]
  intro u hu
  have hg := fullH_domain h ht.1 ht.2 hu.1 (hu.2.trans hce.le)
  simp [gainLiteral,Hratio,gamma5GainLegal,hg.2.2.1.le,hg.2.2.2.1.le]

end Wu2008DoubleSieve.MotherPair
