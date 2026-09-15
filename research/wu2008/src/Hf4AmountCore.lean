import Hf4QuadPublic
import Hf4DEOriginalMass
import Hf4TargetVariation

noncomputable section
namespace Hf4Amount
open Real

theorem payment_cap : Hf4Outer.payment < (1/10000000000 : ℝ) := by
  rw [Hf4DE.payment_exact]
  norm_num

theorem numerator_bounds : (9227603/10000000000 : ℝ) ≤ Hf4Outer.numerator ∧
    Hf4Outer.numerator ≤ (923967/1000000000 : ℝ) := by
  rw [Hf4Outer.numerator_eq_finite]
  have hq := Hf4Quad.original_Q_bounds
  have hv := Hf4Target.new_variation_cap
  have hp := payment_cap
  have hv0 := Hf4Continue.newVariation_pos
  have hp0 := Hf4Outer.payment_pos
  constructor <;> linarith only [hq.1,hq.2,hv,hp,hv0,hp0]

theorem profile_bounds :
    (9227603/10000000000 : ℝ)/(1-858467/5000000) ≤ Hf4Outer.profile ∧
    Hf4Outer.profile ≤ (923967/1000000000 : ℝ)/(1-17169341/100000000) := by
  have hd := Hf4DE.dPaid_bounds
  have hpos := sub_pos.mpr D0FullDensity.dPaid_lt_one
  unfold Hf4Outer.profile
  constructor
  · calc
      _ ≤ (9227603/10000000000 : ℝ)/(1-D0FullDensity.dPaid) :=
        div_le_div_of_nonneg_left (by norm_num) hpos (by linarith only [hd.1])
      _ ≤ _ := div_le_div_of_nonneg_right numerator_bounds.1 hpos.le
  · calc
      _ ≤ (923967/1000000000 : ℝ)/(1-D0FullDensity.dPaid) :=
        div_le_div_of_nonneg_right numerator_bounds.2 hpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith only [hd.2])

/-- Both endpoints enclose the whole currently paid terminal, including V and P. -/
theorem terminal_bounds : (72504/10000000 : ℝ) ≤ Hf4Outer.terminal ∧
    Hf4Outer.terminal ≤ (72516/10000000 : ℝ) := by
  have hp := profile_bounds
  have hpn : 0 ≤ Hf4Outer.profile := by
    have hh := hp.1
    norm_num at hh
    linarith only [hh]
  have hlo := mul_le_mul Hf4Target.log_two_bounds.1.le hp.1
    (by norm_num : (0:ℝ) ≤ (9227603/10000000000)/(1-858467/5000000))
    (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hup := mul_le_mul Hf4Target.log_two_bounds.2.le hp.2 hpn
    (by norm_num : (0:ℝ) ≤ 6932/10000)
  have he := Hf4DE.original_e_mass_bounds
  unfold Hf4Outer.terminal
  norm_num at hlo hup
  constructor <;> linarith only [hlo,hup,he.1,he.2]

theorem terminal_gap_bounds :
    (427/10000000 : ℝ) ≤ NineFeedbackStrength.originalH 8-Hf4Outer.terminal ∧
    NineFeedbackStrength.originalH 8-Hf4Outer.terminal ≤ (439/10000000 : ℝ) := by
  rw [Hf4Target.original_threshold]
  constructor <;> linarith only [terminal_bounds.1,terminal_bounds.2]

theorem whole_paid_terminal_insufficient : Hf4Outer.terminal < NineFeedbackStrength.originalH 8 := by
  have h := terminal_gap_bounds.1
  linarith only [h]

/-- An unconditional numeric bound for the original feedback, not only the paid model. -/
theorem original_feedback_lower : (72504/10000000 : ℝ) ≤
    ActualNineFeedback.firstFeedback NineFeedbackStrength.originalH 3 3 :=
  terminal_bounds.1.trans Hf4Outer.terminal_le_actual

/-- The gap names the original actual remainder; no sufficiency premise is assumed. -/
theorem actual_remaining_gap :
    NineFeedbackStrength.originalH 8 ≤
      ActualNineFeedback.firstFeedback NineFeedbackStrength.originalH 3 3 ↔
    NineFeedbackStrength.originalH 8-Hf4Outer.terminal ≤
      ActualNineFeedback.firstFeedback NineFeedbackStrength.originalH 3 3-Hf4Outer.terminal := by
  exact (sub_le_sub_iff_right Hf4Outer.terminal).symm

end Hf4Amount
