import W09PaidRowsV2

namespace WuTarget.W09
open ActualNineFeedback
noncomputable section

def radius (i : Fin 8) : ℝ :=
  min (1/10) (forcingSlack i.castSucc /
    (8 * (|paidCost i.castSucc| + forcingSlack i.castSucc)))

theorem radius_pos (i : Fin 8) : 0 < radius i := by
  apply lt_min (by norm_num)
  exact div_pos (forcingSlack_pos i)
    (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) (forcingSlack_pos i)))

theorem radius_cap (i : Fin 8) : radius i ≤ 1/10 := min_le_left _ _

theorem debit_le_half_slack (i : Fin 8) {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ radius i) :
    deltaLoss δ * paidCost i.castSucc ≤ forcingSlack i.castSucc / 2 := by
  have hh := hr.trans (radius_cap i)
  have hs := forcingSlack_pos i
  have hp : 0 < 8 * (|paidCost i.castSucc| + forcingSlack i.castSucc) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) hs)
  have hm := (le_div_iff₀ hp).mp (hr.trans (min_le_right _ _))
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (paidCost i.castSucc)) hd.le
  rw [deltaLoss, div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 1 - 2 * δ by linarith only [hh])).mpr
  nlinarith only [hm, hc, mul_nonneg hd.le hs.le,
    mul_nonneg hd.le (abs_nonneg (paidCost i.castSucc))]

def commonRadius : ℝ :=
  min (radius 0) (min (radius 1) (min (radius 2) (min (radius 3)
    (min (radius 4) (min (radius 5) (min (radius 6) (radius 7)))))))

theorem commonRadius_pos : 0 < commonRadius := by
  unfold commonRadius
  repeat' apply lt_min
  all_goals exact radius_pos _

theorem commonRadius_le (i : Fin 8) : commonRadius ≤ radius i := by
  fin_cases i <;> simp [commonRadius, min_le_iff]

theorem commonRadius_cap : commonRadius ≤ 1/10 :=
  (commonRadius_le 0).trans (radius_cap 0)

theorem common_debit_le_half_slack {δ : ℝ} (hd : 0 < δ) (hr : δ ≤ commonRadius)
    (i : Fin 9) : deltaLoss δ * paidCost i ≤ forcingSlack i / 2 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show Fin.last 8 = (8 : Fin 9) from rfl, terminal_cost, terminal_slack]
    norm_num
  · exact debit_le_half_slack j hd (hr.trans (commonRadius_le j))

end
end WuTarget.W09
