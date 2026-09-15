import ActualLogGainScalar
import ActualLogGainPayment

namespace ActualLogGain
open Real Wu2008DoubleSieve HighBoxRecovery
noncomputable section

/-- The literal paid mother is consumed with positive delta, rho and tau.
The same uniform threshold precedes every actual original rectangle. -/
theorem original_upper_fixed_parameters {δ ρ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta)
    (hρ : 0 < ρ) (hρhi : ρ ≤ 1/100)
    (hρexp : ρ*exp (-eulerMascheroniConstant) ≤ 1/100)
    (hτ : 0 < τ) (hτhi : τ ≤ 1/100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (29/10) ≤
        (wuUpperCoefficient (29/10)-1/10000)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (29/10) <
        wuUpperCoefficient (29/10)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hd : δ ≤ 1/10 := by norm_num [highEta] at hδhi; linarith
  obtain ⟨C,_,T0,hT04,hmother⟩ := HighOriginal.log_integral_mother hδ hδhi hρ hτ
    (by norm_num : (0:ℝ)<1/40000)
  obtain ⟨T1,_,hpay⟩ := original_remainder_relative C hδ hδhi
    (by norm_num : (0:ℝ)<1/40000)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hr
  have hm := hmother N ((le_max_left _ _).trans hN) he Δ hlo hhi V hV hr
    (29/10) (31/10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨hθ,hrem⟩ := hpay N ((le_max_right _ _).trans hN) Δ hlo hhi V hV hr
  have hc := mul_le_mul_of_nonneg_right
    (coefficient_gain hd hρ.le hρhi hρexp hτ.le hτhi) hθ.le
  have hupper : wuBoxPhi N δ (convolutionWuWindows N Δ V) (29/10) ≤
      (wuUpperCoefficient (29/10)-1/10000)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    nlinarith only [hm,hrem,hc]
  refine ⟨hθ,hupper,?_⟩
  nlinarith only [hupper,hθ]

/-- Unconditional in the analytic margin and rho/tau witnesses. No Uk count or
abstract H/h limit is used: this is an actual Fin2 upper improvement. -/
theorem original_upper {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (29/10) ≤
        (wuUpperCoefficient (29/10)-1/10000)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (29/10) <
        wuUpperCoefficient (29/10)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
  original_upper_fixed_parameters hδ hδhi rho_bounds.1 rho_bounds.2.1 rho_bounds.2.2
    (by norm_num : (0:ℝ)<1/100) le_rfl

end
end ActualLogGain
