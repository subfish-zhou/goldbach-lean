import RetainedEndpointShapes
import Phase10LogFeedback

namespace Wu2008DoubleSieve.Phase13
open Real Set MeasureTheory HighSixPhase9
noncomputable section

def L0 : ℝ := log (1677/1432)+log (179/130)
def Lend : ℝ := Phase10.L+κh*L0
def rhoEndpoint : ℝ := Phase10.rhoLog+κH+(17/60)*κh+κh*L0/2

theorem endpoint_extra_exact : κH+(17/60)*κh = (4768/847665 : ℝ) := by
  norm_num [κH,κh]

theorem L0_pos : 0 < L0 :=
  add_pos (log_pos (by norm_num)) (log_pos (by norm_num))

theorem rhoEndpoint_strict : Phase10.rhoLog < rhoEndpoint := by
  have hp := mul_pos κh_pos L0_pos
  unfold rhoEndpoint
  linarith only [hp,κh_pos,κH_pos]

/-- The universal logarithm inequality, with no numerical logarithm evaluation. -/
theorem rhoEndpoint_upper : rhoEndpoint ≤ (5852612387/31560263280 : ℝ) := by
  have h1 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1677/1432)
  have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 179/130)
  unfold rhoEndpoint Phase10.rhoLog Phase10.L L0 κh κH
  linarith only [h1,h2]

theorem rhoEndpoint_bounds : 0 < rhoEndpoint ∧ rhoEndpoint < 1 := by
  exact ⟨Phase10.rhoLog_bounds.1.trans rhoEndpoint_strict,
    lt_of_le_of_lt rhoEndpoint_upper (by norm_num)⟩

theorem rhoEndpoint_fixed : rhoEndpoint = Phase10.rhoLog+(4768/847665)+
    κh*(log (1677/1432)+log (179/130))/2 := by
  unfold rhoEndpoint L0
  linarith only [endpoint_extra_exact]

/-- Rewrite the single new pointwise numerator, before integration. -/
theorem endpoint_affine_identity (A u : ℝ) :
    A*(κh+(5/13)*(18/5-(179/50)*u)) =
      A*(κh+18/13)-(A*(179/130))*u := by ring

theorem endpoint_affine_integrable (A : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => A*(κh+(5/13)*(18/5-(179/50)*u))/(u*(1-u)))
      volume (8/13) (129/179) := by
  simp_rw [endpoint_affine_identity]
  exact Phase10.weighted_affine_integrable (by norm_num) (by norm_num) (by norm_num) _ _

/-- True FTC for the whole strengthened numerator on the unchanged weighted window. -/
theorem endpoint_affine_integral (A : ℝ) :
    (∫ u in (8/13 : ℝ)..(129/179),
      A*(κh+(5/13)*(18/5-(179/50)*u))/(u*(1-u))) = A*Lend := by
  simp_rw [endpoint_affine_identity]
  rw [Phase10.weighted_affine_integral (by norm_num) (by norm_num) (by norm_num)]
  norm_num
  unfold Lend Phase10.L L0
  ring

/-- A single comparison of the actual weighted h integral, not two added lower bounds. -/
theorem weighted_h_endpoint_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*Lend ≤
      ∫ u in (8/13 : ℝ)..(129/179),
        wuImprovementLimit false δ ((179/50)*u)/(u*(1-u)) := by
  rw [← endpoint_affine_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (endpoint_affine_integrable _) (weighted_h_integrable hδ hδhi)
  intro u hu
  apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos (by linarith [hu.1])
    (by linarith [hu.2])))
  exact h_retained_linear hδ hδhi ⟨by linarith [hu.1],by linarith [hu.2]⟩

/-- The original first functional supplies its literal half weight and delta penalty. -/
theorem retained_endpoint_first_functional {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    sourceP-penalty δ*envelopeE + amplitude δ*((289/5200)+κH+(17/60)*κh) +
      (1/2)*(amplitude δ*Lend) ≤ amplitude δ := by
  have hf := wuImprovementLimit_firstFunctionalGain
    (s := (13/5 : ℝ)) (t := (179/50 : ℝ)) hδ (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH := H_retained_quadratic hδ hδhi (s := (179/50 : ℝ)) ⟨by norm_num,by norm_num⟩
  have hi := weighted_h_endpoint_lower hδ hδhi
  have hp := psi_delta_raw hδ hδhi
  norm_num only at hf hH
  dsimp [amplitude] at *
  nlinarith only [hf,hH,hi,hp]

theorem amplitude_endpoint_closed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (sourceP-penalty δ*envelopeE)/(1-rhoEndpoint) ≤ amplitude δ := by
  apply (div_le_iff₀ (sub_pos.mpr rhoEndpoint_bounds.2)).2
  have hr := retained_endpoint_first_functional hδ hδhi
  unfold rhoEndpoint Phase10.rhoLog Lend at *
  nlinarith only [hr]

end
end Wu2008DoubleSieve.Phase13
