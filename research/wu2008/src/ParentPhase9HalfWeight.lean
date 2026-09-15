import MathlibNt.Wu2008DoubleSieve.HighSixPhase9LowH

namespace Wu2008DoubleSieve.ParentPhase9HalfWeight
open HighSixPhase9
noncomputable section

/-- The literal first-functional inequality weights its integral by one half. -/
def feedbackRho : ℝ := (289/5200)+(1/2)*(76979/393263)

theorem feedbackRho_eq : feedbackRho = (24138339/157305200 : ℝ) := by
  norm_num [feedbackRho]

theorem feedbackRho_bounds : 0 < feedbackRho ∧ feedbackRho < 1 := by
  norm_num [feedbackRho]

/-- Scalar closure of the actual half-weighted inequality, not the proposed full weight. -/
theorem amplitude_closed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (sourceP-penalty δ*envelopeE)/(1-feedbackRho) ≤ amplitude δ := by
  apply (div_le_iff₀ (sub_pos.mpr feedbackRho_bounds.2)).2
  have hr := retained_first_functional hδ hδhi
  unfold feedbackRho
  linarith only [hr]

/-- The original low-window integral consumes the corrected scalar closure. -/
theorem raw_gain_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    Cgeo*((sourceP-penalty δ*envelopeE)/(1-feedbackRho)) ≤
      SingleUpperHIntegral.gainH34 δ/4 := by
  exact (mul_le_mul_of_nonneg_left (amplitude_closed hδ hδhi) Cgeo_pos.le).trans
    (actual_low_H_amplitude_lower hδ hδhi)

def gainConstant : ℝ := Cgeo*sourceP/(1-feedbackRho)
def penaltyCost : ℝ := Cgeo*envelopeE/(1-feedbackRho)

theorem gainConstant_eq :
    gainConstant = (224077077822547266182001/786669346455967990704800000 : ℝ) := by
  norm_num [gainConstant,Cgeo,sourceP,feedbackRho]

theorem penaltyCost_eq :
    penaltyCost = (2853136658952909/1837809215288800000 : ℝ) := by
  norm_num [penaltyCost,Cgeo,envelopeE,feedbackRho]

theorem gainConstant_pos : 0 < gainConstant := by
  rw [gainConstant_eq]
  norm_num

theorem penaltyCost_pos : 0 < penaltyCost := by
  rw [penaltyCost_eq]
  norm_num

/-- The positive-delta penalty is retained; this is not yet an epsilon-free count. -/
theorem gain_lower_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    gainConstant-penalty δ*penaltyCost ≤ SingleUpperHIntegral.gainH34 δ/4 := by
  have hi := raw_gain_lower hδ hδhi
  have he : gainConstant-penalty δ*penaltyCost =
      Cgeo*((sourceP-penalty δ*envelopeE)/(1-feedbackRho)) := by
    unfold gainConstant penaltyCost
    ring
  rwa [he]

theorem penalty_le {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    penalty δ ≤ (100/49 : ℝ)*δ := by
  unfold penalty
  apply (div_le_iff₀ (by linarith)).2
  nlinarith only [hδ,hδhi]

/-- An explicit linear error bound allows a later common choice of delta. -/
theorem gain_lower_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    gainConstant-((100/49)*penaltyCost)*δ ≤ SingleUpperHIntegral.gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (penalty_le hδ hδhi) penaltyCost_pos.le
  have hi := gain_lower_with_penalty hδ hδhi
  nlinarith only [hp,hi]

end
end Wu2008DoubleSieve.ParentPhase9HalfWeight
