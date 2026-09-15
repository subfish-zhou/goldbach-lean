import MathlibNt.Wu2008DoubleSieve.HighSixPhase9Shape

namespace Wu2008DoubleSieve.HighSixPhase9
open Real Set MeasureTheory
noncomputable section

def sourceP : ℝ := 3629895479136046171/1363514967405501300000
def envelopeE : ℝ := 9563183/659100000
def penalty (δ : ℝ) : ℝ := 2*δ/(1-2*δ)
def rho : ℝ := 39534139/157305200

theorem rho_bounds : 0 < rho ∧ rho < 1 := by norm_num [rho]

/-- The original source retains its explicit fixed-delta penalty. -/
theorem psi_delta_raw {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    sourceP-penalty δ*envelopeE ≤ firstFunctionalGainPsi δ (13/5) (179/50) := by
  rw [firstFunctionalGainPsi_eq_source_sub_penalty (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have hd : 0 ≤ penalty δ := div_nonneg (by linarith) (by linarith)
  have hp := mul_le_mul_of_nonneg_left HighSixPhase5.envelope_upper hd
  dsimp [sourceP,envelopeE,penalty] at *
  linarith only [HighSixPhase5.psi_lower,hp]

/-- The weighted actual lower improvement is genuinely integrable. -/
theorem weighted_h_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    IntervalIntegrable (fun u : ℝ => wuImprovementLimit false δ ((179/50)*u)/(u*(1-u)))
      volume (8/13) (129/179) := by
  convert firstFunctionalGain_limit_intervalIntegrable (s := (13/5 : ℝ))
    (t := (179/50 : ℝ)) hδ (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num

/-- FTC for the affine comparison on the unchanged first-functional window. -/
theorem affine_integral (A : ℝ) :
    (∫ u in (8/13 : ℝ)..(129/179), 4*(A*(5/13)*(18/5-(179/50)*u))) =
      A*(76979/393263) := by
  have hd : ∀ u : ℝ, HasDerivAt
      (fun x : ℝ => 4*(A*(5/13))*((18/5)*x-(179/100)*x^2))
      (4*(A*(5/13)*(18/5-(179/50)*u))) u := by
    intro u
    have hh := (((hasDerivAt_id u).const_mul (18/5)).sub
      (((hasDerivAt_id u).pow 2).const_mul (179/100))).const_mul (4*(A*(5/13)))
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun u : ℝ => 4*(A*(5/13)*(18/5-(179/50)*u)))
      volume (8/13) (129/179) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  calc
    _ = 4*(A*(5/13))*((18/5)*(129/179)-(179/100)*(129/179)^2)-
        4*(A*(5/13))*((18/5)*(8/13)-(179/100)*(8/13)^2) := hf
    _ = _ := by ring

/-- Positivity of the denominator permits payment of the entire affine shape. -/
theorem weighted_h_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*(76979/393263) ≤
      ∫ u in (8/13 : ℝ)..(129/179), wuImprovementLimit false δ ((179/50)*u)/(u*(1-u)) := by
  rw [← affine_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; fun_prop) (weighted_h_integrable hδ hδhi)
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hu1 : 0 < 1-u := by linarith [hu.2]
  have hl := h_linear hδ hδhi (u := (179/50)*u)
    ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hp : 0 ≤ amplitude δ*(5/13)*(18/5-(179/50)*u) :=
    mul_nonneg (mul_nonneg (amplitude_nonneg hδ hδhi) (by norm_num))
      (by linarith [hu.2])
  have hd : u*(1-u) ≤ (1/4 : ℝ) := by nlinarith only [sq_nonneg (u-1/2)]
  have hh := mul_le_mul_of_nonneg_left hd hp
  apply (le_div_iff₀ (mul_pos hu0 hu1)).2
  nlinarith only [hl,hh]

/-- The original interface retains one half of the weighted integral. -/
theorem retained_first_functional {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    sourceP-penalty δ*envelopeE + amplitude δ*(289/5200) +
      (1/2)*(amplitude δ*(76979/393263)) ≤ amplitude δ := by
  have hf := wuImprovementLimit_firstFunctionalGain
    (s := (13/5 : ℝ)) (t := (179/50 : ℝ)) hδ (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH := H_quadratic hδ hδhi (s := (179/50 : ℝ)) ⟨by norm_num,by norm_num⟩
  have hi := weighted_h_lower hδ hδhi
  have hp := psi_delta_raw hδ hδhi
  norm_num only at hf hH
  dsimp [amplitude] at *
  linarith only [hf,hH,hi,hp]

/-- The proposed rho sums the full comparison, not its original half weight. -/
theorem candidate_rho_identity : rho = (289/5200 : ℝ)+(76979/393263) := by
  norm_num [rho]

/-- This strict gap is the precise obstruction in the fixed proposed proof. -/
theorem candidate_rho_exceeds_retained :
    (289/5200 : ℝ)+(1/2)*(76979/393263) < rho := by
  norm_num [rho]

end
end Wu2008DoubleSieve.HighSixPhase9
