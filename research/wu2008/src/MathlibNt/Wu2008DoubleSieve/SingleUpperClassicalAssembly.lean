import MathlibNt.Wu2008DoubleSieve.SingleUpperLowEndpoint
import MathlibNt.Wu2008DoubleSieve.SingleUpperHighQuadrature

namespace Wu2008DoubleSieve.SingleUpperClassicalAssembly
open Real MeasureTheory SingleUpperCounts SingleUpperSplice SingleUpperQuadrature
open SingleUpperClassicalLimit SingleUpperLowEndpoint SingleUpperHighQuadrature
open scoped Classical Topology

/-- The two genuine integrable pieces have exactly the original coefficient. -/
theorem classical_integral_split {δ r : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (hrlo : (1/2-δ)/2 ≤ r) (hrhi : r ≤ 1/3) :
    4*(∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t) +
      4*(∫ t in ((1/2-δ)/2)..r, weight δ t/t) = Gdelta δ r := by
  have ha : (1/15 : ℝ) ≤ truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hb : (1/2-δ)/2 ≤ 1/3 := hrlo.trans hrhi
  have hi1 := density_integrable hδ hδhi ha hab hb
  have hi2 := density_integrable hδ hδhi (ha.trans hab) hrlo hrhi
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  unfold Gdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [weight, div_div, mul_comm]

/-- Full original window, uniform over all endpoints above the actual split. -/
theorem actual_Gdelta_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, (1/2-δ)/2 ≤ r → r ≤ 1/3 →
        (U N r : ℝ) ≤ (Gdelta δ r+ε)*truncatedSixthMassScale N := by
  obtain ⟨TL,hTL,hL⟩ := lowCount_classical_upper hδ hδhi (half_pos hε)
  obtain ⟨TH,_hTH,hH⟩ := actual_high_classical_upper hδ hδhi (half_pos hε)
  refine ⟨max TL TH,hTL.trans (le_max_left _ _),?_⟩
  intro N hN he r hrlo hrhi
  have hl := hL N ((le_max_left _ _).trans hN) he r
  have hh := hH N ((le_max_right _ _).trans hN) he r hrlo hrhi
  have hs := classical_integral_split hδ.le hδhi hrlo hrhi
  rw [count_split]
  change lowCount N δ r + highCount N δ r ≤ _
  calc
    _ ≤ (4*(∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t)+ε/2)*truncatedSixthMassScale N +
        (4*(∫ t in ((1/2-δ)/2)..r, weight δ t/t)+ε/2)*truncatedSixthMassScale N := add_le_add hl hh
    _ = _ := by rw [← hs]; ring

/-- Both original upper endpoints lie beyond the split for every allowed delta. -/
theorem original_endpoint_bounds {δ : ℝ} (hδ : 0 ≤ δ) :
    (1/2-δ)/2 ≤ (1/3 : ℝ) ∧
    (1/2-δ)/2 ≤ truncatedSixthLowerSigma ∧ truncatedSixthLowerSigma ≤ 1/3 := by
  norm_num [truncatedSixthLowerSigma, truncatedSixthLowerAlpha] at *
  constructor <;> linarith

/-- Actual original terms three and four, with their overlap counted twice.
A common positive delta is chosen before the common arithmetic threshold. -/
theorem original_third_fourth_Glin_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (U N (1/3) : ℝ) + (U N truncatedSixthLowerSigma : ℝ) ≤
        (Glin (1/3)+Glin truncatedSixthLowerSigma+ε)*truncatedSixthMassScale N := by
  obtain ⟨δ,hδ,hδhi,hclose⟩ := choose_common_delta (half_pos hε)
  obtain ⟨T,hT,h⟩ := actual_Gdelta_upper hδ hδhi (show 0 < ε/4 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hb := original_endpoint_bounds hδ.le
  have h1 := h N hN he (1/3) hb.1 le_rfl
  have h2 := h N hN he truncatedSixthLowerSigma hb.2.1 hb.2.2
  have hN4 := hT.trans hN
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    have := (wuSingularSeries_pos N (by omega)).le
    positivity
  have hpaid := mul_le_mul_of_nonneg_right hclose.le hscale
  nlinarith [add_le_add h1 h2]

end Wu2008DoubleSieve.SingleUpperClassicalAssembly
