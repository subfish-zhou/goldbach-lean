import Wu18938Campaign.M3.OriginalConsumer
import WR2PsiCostsSuprema
import Wu08OriginalPsiRecovery

noncomputable section

namespace Wu18938Campaign.M3

open Set Real MeasureTheory Wu2008DoubleSieve ActualNineFeedback
open Wu2008DoubleSieve.MotherPair WuPaper.R2Xi WuPaper.R2PsiCosts
open Wu08OriginalPsiRecovery SecondFunctionalSignedCore
open scoped Classical Interval

private theorem uncut_outer_integrable {p : SecondFunctionalParameters}
    (hp : FullHParameters p) (j : Term) (hj : j ≠ .gammaFive)
    {δ : ℝ} (hd : 0 < δ) (hh : δ < 1 / 2) :
    IntervalIntegrable
      (fun t => ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        wuImprovementLimit true δ (Hratio p j t u) / (t * u * (1 - t - u)))
      volume (1 / p.S) (upperP p j) := by
  apply (gain_outer_integrable hp.toAnalyticParameters j hd hh).congr
  intro t ht
  have ht' : t ∈ Icc (1 / p.S) (upperP p j) := by
    simpa only [uIcc_of_le (gain_endpoint_order hp.toAnalyticParameters j).2.1] using
      uIoc_subset_uIcc ht
  apply intervalIntegral.integral_congr
  intro u hu
  apply fullH_gain_literal_eq hp j hj
  apply (pairRegion_iff_slice hp.toAnalyticParameters j ht' u).mpr
  simpa only [uIcc_of_le (gain_start_bounds hp.toAnalyticParameters j ht').2.2] using hu

theorem original67_eq_gain {p : SecondFunctionalParameters}
    (hp : FullHParameters p) (δ : ℝ) :
    original67 (wuImprovementLimit true δ) p = gainIntegral p .gammaSix δ := by
  rw [fullH_gammaSix_integral hp]
  unfold original67
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show p.S - p.S * t - p.S * u = p.S * (1 - t - u) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem original68_eq_gains {p : SecondFunctionalParameters}
    (hp : FullHParameters p) {δ : ℝ} (hd : 0 < δ) (hh : δ < 1 / 2) :
    original68 (wuImprovementLimit true δ) p =
      gainIntegral p .gammaSeven δ + gainIntegral p .gammaEight δ := by
  let f := fun t u => wuImprovementLimit true δ ((1 - t - u) / t) /
    (t * u * (1 - t - u))
  have he := parameter_order hp.toAnalyticParameters
  have hi7 : IntervalIntegrable (fun t => ∫ u in t..(1 / p.kappa1), f t u)
      volume (1 / p.S) (1 / p.kappa1) := by
    apply (uncut_outer_integrable hp .gammaSeven (by decide) hd hh).congr
    intro t ht
    have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa1) := by
      simpa only [upperP, uIcc_of_le he.2.1] using uIoc_subset_uIcc ht
    simp only [upperQ, lowerQ, Hratio, max_eq_right ht'.1, min_eq_right ht'.2]
    rfl
  have hi8 : IntervalIntegrable (fun t => ∫ u in (1 / p.kappa1)..(1 / p.kappa2), f t u)
      volume (1 / p.S) (1 / p.kappa1) := by
    apply (uncut_outer_integrable hp .gammaEight (by decide) hd hh).congr
    intro t ht
    have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa1) := by
      simpa only [upperP, uIcc_of_le he.2.1] using uIoc_subset_uIcc ht
    simp only [upperQ, lowerQ, Hratio, max_eq_left ht'.2, min_eq_right he.2.2.1.le]
    rfl
  rw [fullH_gammaSeven_integral hp, fullH_gammaEight_integral hp]
  change original68 (wuImprovementLimit true δ) p =
    (∫ t in (1 / p.S)..(1 / p.kappa1), ∫ u in t..(1 / p.kappa1), f t u) +
      ∫ t in (1 / p.S)..(1 / p.kappa1), ∫ u in (1 / p.kappa1)..(1 / p.kappa2), f t u
  rw [← intervalIntegral.integral_add hi7 hi8]
  unfold original68
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (1 / p.S) (1 / p.kappa1) := by
    simpa only [uIcc_of_le he.2.1] using ht
  have hint (j : Term) (hj : j ≠ .gammaFive)
      (htj : t ∈ Icc (1 / p.S) (upperP p j)) :
      IntervalIntegrable (fun u => wuImprovementLimit true δ (Hratio p j t u) /
        (t * u * (1 - t - u))) volume
        (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
    apply (gain_inner_integrable hp.toAnalyticParameters j hd hh htj).congr
    intro u hu
    apply fullH_gain_literal_eq hp j hj
    apply (pairRegion_iff_slice hp.toAnalyticParameters j htj u).mpr
    simpa only [uIcc_of_le (gain_start_bounds hp.toAnalyticParameters j htj).2.2] using
      uIoc_subset_uIcc hu
  have h7 : IntervalIntegrable (f t) volume t (1 / p.kappa1) := by
    simpa only [upperQ, lowerQ, Hratio, max_eq_right ht'.1, min_eq_right ht'.2] using
      hint .gammaSeven (by decide) ht'
  have h8 : IntervalIntegrable (f t) volume (1 / p.kappa1) (1 / p.kappa2) := by
    simpa only [upperQ, lowerQ, Hratio, max_eq_left ht'.2, min_eq_right he.2.2.1.le] using
      hint .gammaEight (by decide) ht'
  dsimp only
  rw [intervalIntegral.integral_add_adjacent_intervals h7 h8,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [f]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem original_feedback_difference {p : SecondFunctionalParameters}
    (hp : FullHParameters p) {δ : ℝ} (hd : 0 < δ) (hh : δ < 1 / 2) :
    originalSecondFeedback δ p -
      (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
        actualLowerJ δ p.s p.S + actualLowerJ δ p.kappa2 p.S +
        actualLowerJ δ p.kappa3 p.S +
        ∫ v in (1 : ℝ)..3,
          wuImprovementLimit true δ v * SecondFunctionalCoupledFeedback.density p v) / 5 =
      (original66 (wuImprovementLimit true δ) p - gainIntegral p .gammaFive δ) / 5 := by
  have hi := SecondFunctionalCoupledFeedback.four_gain_identity p hp.toAnalyticParameters hd hh
  unfold fourIntegralUpper SecondFunctionalCoupledFeedback.classical at hi
  unfold originalSecondFeedback
  rw [original67_eq_gain hp, original68_eq_gains hp hd hh]
  linarith only [hi]

theorem original_functional_gap {p : SecondFunctionalParameters}
    (hp : FullHParameters p) (hg : CoupledGeometry p)
    {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    (classicalNumerator p / 5 - 2 * originalCost p / (5 * (1 - 2 * δ)) +
        originalSecondFeedback δ p) -
      (wuUpperCoefficient p.s +
        (SecondFunctionalCoupledFeedback.gain p δ -
          SecondFunctionalCoupledFeedback.cost p δ) / 5) =
      (original66 (wuImprovementLimit true δ) p - gainIntegral p .gammaFive δ -
        (2 / (1 - 2 * δ)) *
          (separationGap p +
            (phiSup (fun phi => SecondFunctionalCoupled.kernel p phi +
              missingKernel p phi - unitKernel p phi) - SecondFunctionalCoupled.jointSup p))) / 5 := by
  have hb := coupled_geometry_bounds hg
  have hhalf : δ < 1 / 2 := by linarith
  have hs := J_split hd hhalf hb.1 hb.2.1 hg.1.three_le_S hg.1.S_le_five hg.2.2.1
  have h2 := J_split hd hhalf hb.2.2.1 hb.2.2.2.1
    hg.1.three_le_S hg.1.S_le_five hg.2.2.2.1
  have h3 := J_split hd hhalf hb.2.2.2.2.1 hb.2.2.2.2.2.1
    hg.1.three_le_S hg.1.S_le_five hg.2.2.2.2
  have hc := coupledBase_eq_original_logs hg
  have hf := original_feedback_difference hp hd hhalf
  have hcost := originalCost_exact_coupled p hg.1.mother hb.1
  have hcost' := congrArg (fun x : ℝ => (2 / (1 - 2 * δ)) * x) hcost
  unfold coupledBase at hc
  unfold SecondFunctionalCoupledFeedback.gain SecondFunctionalCoupledFeedback.cost
  rw [hs, h2, h3]
  unfold actualLowerJ at hf
  unfold lowerGain
  unfold coupledCostMass at hcost' hc
  simp only [div_eq_mul_inv, mul_inv_rev] at hc hf hcost' ⊢
  ring_nf at hc hf hcost' ⊢
  linarith only [hc, hf, hcost']

theorem original_four_functional_comparison_iff (r : Fin 4)
    {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    (classicalNumerator (coupledRow r) / 5 -
        2 * originalCost (coupledRow r) / (5 * (1 - 2 * δ)) +
        originalSecondFeedback δ (coupledRow r) ≤
      wuUpperCoefficient (coupledRow r).s +
        (SecondFunctionalCoupledFeedback.gain (coupledRow r) δ -
          SecondFunctionalCoupledFeedback.cost (coupledRow r) δ) / 5) ↔
    original66 (wuImprovementLimit true δ) (coupledRow r) -
        gainIntegral (coupledRow r) .gammaFive δ ≤
      (2 / (1 - 2 * δ)) *
        (separationGap (coupledRow r) +
          (phiSup (fun phi => SecondFunctionalCoupled.kernel (coupledRow r) phi +
            missingKernel (coupledRow r) phi - unitKernel (coupledRow r) phi) -
            SecondFunctionalCoupled.jointSup (coupledRow r))) := by
  have hp : FullHParameters (coupledRow r) := by
    fin_cases r
    · exact row1_fullH
    · exact row2_fullH
    · exact row3_fullH
    · exact row4_fullH
  have h := original_functional_gap hp (coupledRow_geometry r) hd hh
  constructor <;> intro hle <;> linarith only [h, hle]

end Wu18938Campaign.M3
