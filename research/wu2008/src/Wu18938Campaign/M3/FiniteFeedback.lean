import WSrcNineCertificate

noncomputable section

namespace Wu18938Campaign.M3

open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open WuTarget

theorem finite_increment_nonneg (i : Fin 9) : 0 ≤ W09.increment i := by
  refine Fin.lastCases ?_ (fun j => (W09.increment_pos j).le) i
  norm_num [W09.increment]

private theorem finite_slack_nonneg (i : Fin 9) : 0 ≤ W09.forcingSlack i := by
  linarith only [finite_increment_nonneg i, W09.increment_le_half_slack i]

theorem finite_debit_bound {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ WuSource.SrcNine.d) (i : Fin 9) :
    deltaLoss δ * W09.paidCost i ≤ 5 / 16 * W09.forcingSlack i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show Fin.last 8 = (8 : Fin 9) from rfl,
      W09.terminal_cost, W09.terminal_slack]
    ring_nf
    exact le_rfl
  · have hrj : δ ≤ W09.radius j :=
      hr.trans (W09.commonRadius_le j)
    have hh := hrj.trans (W09.radius_cap j)
    have hs := W09.forcingSlack_pos j
    have hp : 0 < 8 * (|W09.paidCost j.castSucc| + W09.forcingSlack j.castSucc) :=
      mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) hs)
    have hm := (le_div_iff₀ hp).mp (hrj.trans (min_le_right _ _))
    have hc := mul_le_mul_of_nonneg_left
      (le_abs_self (W09.paidCost j.castSucc)) hd.le
    rw [deltaLoss, div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 1 - 2 * δ by linarith only [hh])).mpr
    nlinarith only [hm, hc, mul_nonneg hd.le hs.le,
      mul_nonneg (show 0 ≤ 1 / 10 - δ by linarith only [hh]) hs.le]

def finiteProfile (i : Fin 9) : ℝ :=
  WuSource.SrcNine.z i + 3 / 8 * W09.increment i

theorem finite_profile_dominates (i : Fin 9) :
    WuSource.SrcNine.z i ≤ finiteProfile i :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (finite_increment_nonneg i))

theorem finite_profile_nonneg (i : Fin 9) : 0 ≤ finiteProfile i :=
  (WuSource.SrcNine.z_positive i).le.trans (finite_profile_dominates i)

theorem finite_profile_strict (i : Fin 8) :
    WuSource.SrcNine.z i.castSucc < finiteProfile i.castSucc :=
  lt_add_of_pos_right _ (mul_pos (by norm_num) (W09.increment_pos i))

theorem finite_profile_actual {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ WuSource.SrcNine.d) (i : Fin 9) :
    finiteProfile i ≤ actualNine δ i := by
  have hz := WuSource.SrcNine.actual_nine_lower hd hr
  have hm := (W17Joint.symbolic_apply_le_feedback
      (fun k => (WuSource.SrcNine.z_positive k).le) i).trans
    (matrixApply_mono feedbackMatrix_nonneg hz i)
  have hrow := WuSource.SrcNine.all_rows i
  rw [W09.seed_eq_publication_add_increment] at hrow
  have hactual := W09.actual_with_loss hd (hr.trans WuSource.SrcNine.d_cap) i
  have hdebit := finite_debit_bound hd hr i
  have hinc := W09.increment_le_half_slack i
  unfold finiteProfile
  linarith only [hm, hrow, hactual, hdebit, hinc]

theorem finite_profile_H {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ WuSource.SrcNine.d) (i : Fin 9) :
    WuSource.SrcNine.z i + 3 / 8 * W09.increment i ≤
      wuImprovementLimit true δ ((22 + (i.val : ℝ)) / 10) :=
  finite_profile_actual hd hr i

end Wu18938Campaign.M3
