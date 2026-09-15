import HighOriginalMother
import MathlibNt.Wu2008DoubleSieve.PositiveGainSeed
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource

namespace ActualLogGain
open Real Wu2008DoubleSieve
noncomputable section

/-- Reuses the pre-existing fixed analytic seed; no new endpoint is chosen. -/
theorem fixed_seed {δ : ℝ} (hδ : δ ≤ 1/10) :
    (1/5000 : ℝ) ≤ wuUpperCoefficient (29/10)-wuUpperCoefficient (31/10)+
      (∫ u in (1-1/(29/10 : ℝ))..(1-1/(31/10 : ℝ)),
        log ((31/10)*u-1)/(u*(1-u)))/2-
      omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ) := by
  rw [firstFunctionalGain_coefficient_eq_log (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  convert positiveGain_explicit_seed hδ using 1
  norm_num
  ring

/-- Finite-positive-delta bound on the original unbounded-phi supremum. -/
theorem envelope_div_bound {δ : ℝ} (hδ : δ ≤ 1/10) :
    0 ≤ omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ) ∧
    omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ) ≤ 31/146334 := by
  have hE := (omega3XIntegralEnvelope_bounds
    (by norm_num : (2:ℝ)≤29/10) (by norm_num : (29/10:ℝ)≤31/10)
    (by norm_num : (31/10:ℝ)≤10)).1
  have hI := positiveGain_envelope_le_simplex
    (by norm_num : (2:ℝ)≤29/10) (by norm_num : (29/10:ℝ)≤31/10)
    (by norm_num : (31/10:ℝ)≤10)
  norm_num at hI
  refine ⟨div_nonneg hE (by linarith), ?_⟩
  apply (div_le_iff₀ (show 0 < 1-2*δ by linarith)).mpr
  linarith

/-- The rho/tau errors are paid, not silently replaced by their zero limits. -/
theorem density_debit {δ ρ τ : ℝ} (hδ : δ ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρhi : ρ ≤ 1/100)
    (hρexp : ρ*exp (-eulerMascheroniConstant) ≤ 1/100)
    (_hτ : 0 ≤ τ) (hτhi : τ ≤ 1/100) :
    (1+τ)*HighO3.densityFactor δ ρ/8*omega3XIntegralEnvelope (29/10) (31/10) ≤
      omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ)+1/20000 := by
  have hfactor : (1+τ)*(1+ρ)*(1+ρ*exp (-eulerMascheroniConstant)) ≤ (6/5:ℝ) := by
    have hh : (1+τ)*(1+ρ)*(1+ρ*exp (-eulerMascheroniConstant)) ≤
        (101/100:ℝ)*(101/100)*(101/100) := by
      gcongr <;> linarith
    linarith only [hh]
  obtain ⟨hE,hI⟩ := envelope_div_bound hδ
  have hp := mul_le_mul_of_nonneg_right hfactor hE
  have he : (1+τ)*HighO3.densityFactor δ ρ/8*omega3XIntegralEnvelope (29/10) (31/10) =
      ((1+τ)*(1+ρ)*(1+ρ*exp (-eulerMascheroniConstant)))*
        (omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ)) := by
    unfold HighO3.densityFactor
    ring
  rw [he]
  linarith only [hp,hI]

/-- Strict positive coefficient improvement with the actual positive-parameter factor. -/
theorem coefficient_gain {δ ρ τ : ℝ} (hδ : δ ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρhi : ρ ≤ 1/100)
    (hρexp : ρ*exp (-eulerMascheroniConstant) ≤ 1/100)
    (hτ : 0 ≤ τ) (hτhi : τ ≤ 1/100) :
    wuUpperCoefficient (31/10)-
      (∫ u in (1-1/(29/10 : ℝ))..(1-1/(31/10 : ℝ)),
        log ((31/10)*u-1)/(u*(1-u)))/2+
      (1+τ)*HighO3.densityFactor δ ρ/8*omega3XIntegralEnvelope (29/10) (31/10) ≤
        wuUpperCoefficient (29/10)-3/20000 := by
  have hs := fixed_seed hδ
  have hd := density_debit hδ hρ hρhi hρexp hτ hτhi
  linarith only [hs,hd]

/-- A genuinely positive parameter, with no numerical evaluation of exp. -/
def rho : ℝ := 1/(100*(1+exp (-eulerMascheroniConstant)))

theorem rho_bounds : 0 < rho ∧ rho ≤ 1/100 ∧
    rho*exp (-eulerMascheroniConstant) ≤ 1/100 := by
  have he := exp_pos (-eulerMascheroniConstant)
  have hd : 0 < 100*(1+exp (-eulerMascheroniConstant)) := by positivity
  refine ⟨by unfold rho; positivity, ?_, ?_⟩
  · unfold rho
    apply (div_le_iff₀ hd).mpr
    linarith
  · unfold rho
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    linarith

end
end ActualLogGain
