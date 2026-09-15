import InsertedO2Payment
import InsertedO2Quadrature
import HighO2TerminalScalar

namespace InsertedO2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2 HighO2Terminal
open scoped Classical Topology Interval
noncomputable section

/-- Full literal prime Omega2 on every once-inserted actual Fin3 box.
Same δ, arbitrary ε, and a threshold before all moving endpoints and s,t.
This is not an all-depth or a positive-h assertion. -/
theorem inserted_log_integral_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      ((∫ u in (1-1/s)..(1-1/t), log (t*u-1)/(u*(1-u)))-ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  let e : ℝ := min 1 (ε/42)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heb : 42*e ≤ ε := by
    have := min_le_right (1 : ℝ) (ε/42)
    dsimp [e]
    linarith
  obtain ⟨T0,hT04,hcount⟩ := prime_lower hδ.le he he1
  obtain ⟨T1,_,hquad⟩ := selected_integral hδ.le he
  obtain ⟨T2,_,hAP⟩ := inserted_AP_relative hδ hδhi he
  obtain ⟨T3,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T0 (max T1 (max T2 T3)),hT04.trans (le_max_left _ _),?_⟩
  intro N hN hEven Δ hlo hhi V hV hr U hU s t hs hst ht ht5 hc
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN3 : T3 ≤ N := by omega
  have hN4 := hT04.trans hN0
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN3 Δ hlo hhi
  have hg := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hU
  have hfinite := hcount N hN0 hEven 3 (convolutionWuWindows N Δ (Fin.cons U V))
    (fun j p hp => (hg.1 j p hp).1) hg.2 s t hs ht ht5 hc
  have hquadrature := hquad N hN1 3 (convolutionWuWindows N Δ (Fin.cons U V))
    (fun j p hp => (hg.1 j p hp).1) hg.2 (logCoefficient e)
    ((logCoefficient_monotone e).monotoneOn _) (logCoefficient_bounded he.le he1)
    s t hs hst ht ht5
  have hap := hAP N hN2 Δ hlo hhi V hV hr U hU
  have hlocal := mul_le_mul_of_nonneg_right
    (log_integral_slack he.le hs hst ht ht5 hc) hap.1
  have hbudget := mul_le_mul_of_nonneg_right heb hap.1
  have hq := (abs_le.mp hquadrature).1
  nlinarith only [hfinite,hap.2,hlocal,hbudget,hq]

end
end InsertedO2
