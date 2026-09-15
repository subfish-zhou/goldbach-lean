import CoupledEndpointShapes
import CompleteReciprocalGain
import Phase10LogFeedback

namespace Wu2008DoubleSieve.Phase17
open Real Set MeasureTheory HighSixPhase9
noncomputable section

def L0 : ℝ := log (1677/1432)+log (179/130)
def Lend : ℝ := Phase10.L+κX*L0
def rhoCoupled : ℝ := Phase10.rhoLog+κY+(17/60)*κX+κX*L0/2

theorem L0_pos : 0 < L0 :=
  add_pos (log_pos (by norm_num)) (log_pos (by norm_num))

theorem rhoCoupled_strict : Phase10.rhoLog < rhoCoupled := by
  have hp := mul_pos κX_pos L0_pos
  unfold rhoCoupled
  linarith only [hp,κX_pos,κY_pos]

/-- The universal logarithm inequality, with no numerical logarithm evaluation. -/
theorem rhoCoupled_upper : rhoCoupled ≤ (1066145005621/5711754232080 : ℝ) := by
  have h1 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1677/1432)
  have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 179/130)
  unfold rhoCoupled Phase10.rhoLog Phase10.L L0 κX κY
  linarith only [h1,h2]

theorem rhoCoupled_bounds : 0 < rhoCoupled ∧ rhoCoupled < 1 := by
  exact ⟨Phase10.rhoLog_bounds.1.trans rhoCoupled_strict,
    lt_of_le_of_lt rhoCoupled_upper (by norm_num)⟩

/-- Improvement is solely the coupled feedback, not a new kernel. -/
theorem rhoCoupled_gt_endpoint : Phase13.rhoEndpoint < rhoCoupled := by
  have hX : 0 < κX-Phase13.κh := by norm_num [κX,Phase13.κh]
  have hY : 0 < κY-Phase13.κH := by norm_num [κY,Phase13.κH]
  have hp := mul_pos hX L0_pos
  unfold rhoCoupled Phase13.rhoEndpoint L0 Phase13.L0 at *
  nlinarith only [hX,hY,hp]

/-- Rewrite the single new pointwise numerator, before integration. -/
theorem endpoint_affine_identity (A u : ℝ) :
    A*(κX+(5/13)*(18/5-(179/50)*u)) =
      A*(κX+18/13)-(A*(179/130))*u := by ring

theorem endpoint_affine_integrable (A : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => A*(κX+(5/13)*(18/5-(179/50)*u))/(u*(1-u)))
      volume (8/13) (129/179) := by
  simp_rw [endpoint_affine_identity]
  exact Phase10.weighted_affine_integrable (by norm_num) (by norm_num) (by norm_num) _ _

/-- True FTC for the whole strengthened numerator on the unchanged weighted window. -/
theorem endpoint_affine_integral (A : ℝ) :
    (∫ u in (8/13 : ℝ)..(129/179),
      A*(κX+(5/13)*(18/5-(179/50)*u))/(u*(1-u))) = A*Lend := by
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
  exact hCoupled hδ hδhi ⟨by linarith [hu.1],by linarith [hu.2]⟩

/-- The original first functional supplies its literal half weight and delta penalty. -/
theorem retained_endpoint_first_functional {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    sourceP-penalty δ*envelopeE + amplitude δ*((289/5200)+κY+(17/60)*κX) +
      (1/2)*(amplitude δ*Lend) ≤ amplitude δ := by
  have hf := wuImprovementLimit_firstFunctionalGain
    (s := (13/5 : ℝ)) (t := (179/50 : ℝ)) hδ (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH := HCoupled hδ hδhi (s := (179/50 : ℝ)) ⟨by norm_num,by norm_num⟩
  have hi := weighted_h_endpoint_lower hδ hδhi
  have hp := psi_delta_raw hδ hδhi
  norm_num only at hf hH
  dsimp [amplitude] at *
  nlinarith only [hf,hH,hi,hp]

theorem amplitudeClosedCoupled {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (sourceP-penalty δ*envelopeE)/(1-rhoCoupled) ≤ amplitude δ := by
  apply (div_le_iff₀ (sub_pos.mpr rhoCoupled_bounds.2)).2
  have hr := retained_endpoint_first_functional hδ hδhi
  unfold rhoCoupled Phase10.rhoLog Lend at *
  nlinarith only [hr]

open SingleUpperHIntegral
open Phase16 (C16 C16_pos M_pos movingC movingC_bounds actual_low_H_reciprocal_lower)

def g17 : ℝ := C16*sourceP/(1-rhoCoupled)
def B17 : ℝ := Phase16.M*sourceP/(1-rhoCoupled)+(100/49)*C16*envelopeE/(1-rhoCoupled)

theorem g17_pos : 0 < g17 :=
  div_pos (mul_pos C16_pos (by norm_num [sourceP])) (sub_pos.mpr rhoCoupled_bounds.2)

theorem B17_pos : 0 < B17 := by
  unfold B17
  exact add_pos (div_pos (mul_pos M_pos (by norm_num [sourceP])) (sub_pos.mpr rhoCoupled_bounds.2))
    (div_pos (mul_pos (mul_pos (by norm_num) C16_pos) (by norm_num [envelopeE]))
      (sub_pos.mpr rhoCoupled_bounds.2))

/-- Positive moving coefficients pay the amplitude from below; no upper amplitude bound. -/
theorem gain17_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g17-B17*δ ≤ gainH34 δ/4 := by
  have hc := movingC_bounds hδ hδhi
  have hd := sub_pos.mpr rhoCoupled_bounds.2
  have hp : 0 < sourceP := by norm_num [sourceP]
  have he : 0 < envelopeE := by norm_num [envelopeE]
  have hpen : 0 ≤ penalty δ := by
    unfold penalty
    exact div_nonneg (by positivity) (by linarith)
  have hA := (mul_le_mul_of_nonneg_left (amplitudeClosedCoupled hδ hδhi) hc.1).trans
    (actual_low_H_reciprocal_lower hδ hδhi)
  have hP := mul_le_mul_of_nonneg_right hc.2.2 (div_pos hp hd).le
  have hE := mul_le_mul_of_nonneg_right hc.2.1 (mul_nonneg hpen (div_pos he hd).le)
  have hpenhi := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    (div_pos (mul_pos C16_pos he) hd).le
  have hrewrite : movingC δ*((sourceP-penalty δ*envelopeE)/(1-rhoCoupled)) =
      movingC δ*(sourceP/(1-rhoCoupled))-movingC δ*(penalty δ*(envelopeE/(1-rhoCoupled))) := by ring
  rw [hrewrite] at hA
  unfold g17 B17
  simp only [div_eq_mul_inv] at hP hE hpenhi hA ⊢
  nlinarith only [hP,hE,hpenhi,hA]


end
end Wu2008DoubleSieve.Phase17
