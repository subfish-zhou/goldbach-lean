import MathlibNt.Wu2008DoubleSieve.SingleUpperHPackingEndpoint

namespace Wu2008DoubleSieve.TruncatedElevenHIntegralCount
open Finset Set Real MeasureTheory
open SingleUpperHIntegral SingleUpperHPackingEndpoint SingleUpperHFineCoarse
open SingleUpperHAssembly SingleUpperClassicalAssembly SingleUpperClassicalLimit
open SingleUpperLowPacking SingleUpperCounts TruncatedElevenHPackedCount
open scoped Classical

/-- The two original low segments are paid twice, each with its factor four. -/
theorem pair_coefficient {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    8*(∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t)+highCoefficient δ =
      Gdelta δ (1/3)+Gdelta δ truncatedSixthLowerSigma-gainH34 δ := by
  have hb := original_endpoint_bounds hδ.le
  have h1 := classical_integral_split hδ.le hδhi hb.1 le_rfl
  have h2 := classical_integral_split hδ.le hδhi hb.2.1 hb.2.2
  have hl := low_integral_split hδ hδhi
  dsimp [highCoefficient,gainH34]
  linarith only [h1,h2,hl]

/-- Integral upper for the actual packed pair, with internal source/grid choices. -/
theorem packed_pair_integral_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ n : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      packed34 (fullGrid δ n) N δ η Δ ≤
        (Gdelta δ (1/3)+Gdelta δ truncatedSixthLowerSigma-gainH34 δ+ε)*truncatedSixthMassScale N := by
  obtain ⟨n,η,hη,T,hT,hP⟩ := packing_integral_upper hδ hδhi (half_pos hε)
  refine ⟨n,η,hη,T,hT,?_⟩
  intro N hN Δ hΔlo hΔhi
  have hp := hP N hN Δ hΔlo hΔhi
  have hc := pair_coefficient hδ hδhi
  unfold packed34
  rw [← hc]
  linarith only [hp]

/-- Actual original U3+U4, not a difference of unrelated count uppers. -/
theorem actual_pair_integral_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (U N (1/3) : ℝ)+(U N truncatedSixthLowerSigma : ℝ) ≤
        (Gdelta δ (1/3)+Gdelta δ truncatedSixthLowerSigma-gainH34 δ+ε)*truncatedSixthMassScale N := by
  obtain ⟨n,η,hη,TP,hTP,hP⟩ := packed_pair_integral_upper hδ hδhi (half_pos hε)
  obtain ⟨TU,_,hU⟩ := actual_pair_upper hδ hδhi hη (half_pos hε)
    (fullGrid δ n) (fullGrid_anchor δ n) (fullGrid_legal hδhi n)
  refine ⟨max TP TU,hTP.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hNP := (le_max_left TP TU).trans hN
  have hNU := (le_max_right TP TU).trans hN
  have hN2 : 2 ≤ N := by have := hTP.trans hNP; omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpΔ := rpow_pos_of_pos hlog (-4 : ℝ)
  have hp := hP N hNP (1+log (N : ℝ)^(-4 : ℝ)) le_rfl (by linarith)
  have hu := hU N hNU he (1+log (N : ℝ)^(-4 : ℝ)) le_rfl (by linarith)
  linarith only [hp,hu]


end Wu2008DoubleSieve.TruncatedElevenHIntegralCount
