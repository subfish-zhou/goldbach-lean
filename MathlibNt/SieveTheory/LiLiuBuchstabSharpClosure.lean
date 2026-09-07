import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosureBounds

set_option autoImplicit false

open Set

namespace LiLiuBuchstabSharp

/-- The actual Buchstab function on the entire starting unit window. -/
theorem buchstab_sharp_window_closed {u : ℝ}
    (hu : (17 / 4 : ℝ) ≤ u) (hu' : u ≤ (21 / 4 : ℝ)) :
    LiLiuPrereqBuchstab.buchstab u ≤ (561522 / 1000000 : ℝ) := by
  by_cases h : u ≤ 5
  · have he := (buchstab_sharp_window_left_enclosure hu h).2
    have hb := rationalStage_two_sharp hu h
    linarith
  · have h5 : (5 : ℝ) ≤ u := le_of_lt (lt_of_not_ge h)
    have he := (buchstab_sharp_window_right_enclosure h5 hu').2
    have hb := rationalStage_three_sharp h5 hu'
    linarith

/-- Requested sharp upper bound for the actual Buchstab function on the full tail.
This only consumes the pre-existing tail-propagation theorem. -/
theorem buchstab_sharp_tail_closed {u : ℝ} (hu : (17 / 4 : ℝ) ≤ u) :
    LiLiuPrereqBuchstab.buchstab u ≤ (561522 / 1000000 : ℝ) := by
  apply LiLiuPrereqBuchstab.buchstab_upper_on_tail (a := (17 / 4 : ℝ))
    (by norm_num) _ u hu
  intro v hv
  exact buchstab_sharp_window_closed hv.1 (by linarith [hv.2])

end LiLiuBuchstabSharp