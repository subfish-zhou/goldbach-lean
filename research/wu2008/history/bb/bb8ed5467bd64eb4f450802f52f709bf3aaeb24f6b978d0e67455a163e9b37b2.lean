import MathlibNt.Wu2008DoubleSieve.TableGainClip

/-!
# Actual lower gain from the clipped logarithmic partition

Wu08 (3.8) integrates H(u)/u. Clipping beyond an original right
endpoint collapses that cell; antitonicity is used only otherwise.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped BigOperators Interval

theorem tableGain_actual_lower_cell {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs6 : s ≤ 6)
    (i : Fin 29) :
    tableGainWeight s i * wuImprovementLimit true δ (tableFeedbackR (i.val + 1)) ≤
      ∫ u in tableGainClip s i.val..tableGainClip s (i.val + 1),
        wuImprovementLimit true δ u / u := by
  by_cases hcollapse : tableFeedbackR (i.val + 1) ≤ s - 1
  · obtain ⟨hl, hr⟩ := tableGainClip_collapse hcollapse
    rw [tableGainWeight_collapse hcollapse, hl, hr, intervalIntegral.integral_same]
    simp
  · have hright : tableGainClip s (i.val + 1) = tableFeedbackR (i.val + 1) :=
      max_eq_right (le_of_lt (lt_of_not_ge hcollapse))
    have hHK := wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
      (a := s - 1) (b := 5) (by linarith) (by linarith) (by norm_num)
    have hR := tableGainR_bounds (n := i.val + 1) (by omega)
    rw [← tableGainWeight_integral, mul_comm _ (wuImprovementLimit true δ _),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (tableGainClip_monotone s (Nat.le_succ i.val))
      ((tableGainClip_reciprocal_intervalIntegrable s i.val).const_mul _)
      (hHK.mono_set (tableGainClip_cell_subset hs6 i.isLt))
    intro u hu
    have hu1 : 1 ≤ u := by
      have hleft := (tableGainClip_bounds hs6 (by omega : i.val ≤ 29)).1
      linarith [hu.1]
    have hur : u ≤ tableFeedbackR (i.val + 1) := by simpa only [hright] using hu.2
    have hH := wuImprovementLimit_upper_antitone hδ hδhi
      ⟨hu1, by linarith [hR.2]⟩ ⟨hR.1, by linarith [hR.2]⟩ hur
    have hm := mul_le_mul_of_nonneg_right hH
      (one_div_nonneg.mpr (by linarith : 0 ≤ u))
    simpa only [div_eq_mul_inv, one_mul] using hm

theorem tableGain_actual_lower_integral {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    (∑ i : Fin 29, tableGainWeight s i *
      wuImprovementLimit true δ (tableFeedbackR (i.val + 1))) ≤
      ∫ u in (s - 1)..5, wuImprovementLimit true δ u / u := by
  have hHK := wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
    (a := s - 1) (b := 5) (by linarith) (by linarith) (by norm_num)
  calc
    _ ≤ ∑ i : Fin 29, ∫ u in tableGainClip s i.val..tableGainClip s (i.val + 1),
        wuImprovementLimit true δ u / u :=
      Finset.sum_le_sum (fun i _ => tableGain_actual_lower_cell hδ hδhi hs hs6 i)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        ∫ u in tableGainClip s k..tableGainClip s (k + 1),
          wuImprovementLimit true δ u / u) 29]
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (a := tableGainClip s) (n := 29)
        (fun k hk => hHK.mono_set (tableGainClip_cell_subset (k := k) hs6 hk)),
        tableGainClip_first hs, tableGainClip_last hs6]

theorem tableGain_actual_clipped_lower {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    (∑ i : Fin 29, tableGainWeight s i *
      wuImprovementLimit true δ (tableFeedbackR (i.val + 1))) ≤
      wuImprovementLimit false δ s := by
  have hpart := tableGain_actual_lower_integral hδ hδhi hs hs6
  have hcross := (wu08_38 hδ hδhi hs hs6 (by norm_num : (6 : ℝ) ≤ 10)).1
  have h6 := wuImprovementLimit_nonneg false hδ (by linarith)
    (by norm_num : (1 : ℝ) ≤ 6) (by norm_num : (6 : ℝ) ≤ 10)
  norm_num only [show (6 : ℝ) - 1 = 5 by norm_num] at hcross
  linarith

theorem tableGainWeight_six (i : Fin 29) : tableGainWeight 6 i = 0 := by
  apply tableGainWeight_collapse
  have hb := (tableGainR_bounds (n := i.val + 1) (by omega)).2
  linarith

end Wu2008DoubleSieve
