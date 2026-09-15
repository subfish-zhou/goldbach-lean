import HighO2TerminalPayment
import HighO2TerminalScalar
import HighO2TerminalQuadrature

namespace HighO2Terminal
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2
open scoped Classical Topology Interval
noncomputable section

/-- The full actual Omega2 lower on the original logarithmic integral domain.
The selected-prime deletion, local density slack, quadrature and single AP
error are all paid before the threshold, uniformly in the moving boxes. -/
theorem original_log_integral_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      ((∫ u in (1-1/s)..(1-1/t), log (t*u-1)/(u*(1-u)))-ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  let e : ℝ := min 1 (ε/42)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heb : 42*e ≤ ε := by
    have := min_le_right (1 : ℝ) (ε/42)
    dsimp [e]
    linarith
  obtain ⟨T0,hT04,hcount⟩ := original_prime_lower hδ.le hδhi he he1
  obtain ⟨T1,_,hquad⟩ := original_selected_integral hδ.le hδhi he
  obtain ⟨T2,_,hAP⟩ := original_AP_relative hδ hδhi he
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN hEven Δ hlo hhi V hV hr s t hs hst ht ht5 hc
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hΔ : 0 < Δ := by
    have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have := rpow_nonneg hlog (-4 : ℝ)
    linarith
  have hfinite := hcount N hN0 hEven Δ hΔ V hV hr s t hs hst ht ht5 hc
  have hquadrature := hquad N hN1 Δ hΔ V hV hr (logCoefficient e)
    ((logCoefficient_monotone e).monotoneOn _) (logCoefficient_bounded he.le he1)
    s t hs hst ht ht5
  have hap := hAP N hN2 Δ hlo hhi V hV hr
  have hlocal := mul_le_mul_of_nonneg_right
    (log_integral_slack he.le hs hst ht ht5 hc) hap.1
  have hbudget := mul_le_mul_of_nonneg_right heb hap.1
  have hq := (abs_le.mp hquadrature).1
  nlinarith only [hfinite,hap.2,hlocal,hbudget,hq]

end
end HighO2Terminal
