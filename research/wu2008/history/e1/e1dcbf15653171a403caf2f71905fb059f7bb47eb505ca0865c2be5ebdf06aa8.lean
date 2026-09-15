import MathlibNt.Wu2008DoubleSieve.TableGainUpper

/-!
# The extended source grid and its actual endpoint transport

The first nine rows retain the seed coordinates identically. Only the
remaining twenty rows use the proved upper-tail integral transport.
-/

namespace Wu2008DoubleSieve

open Set Real
open scoped BigOperators Matrix

theorem tableGainR_last : tableFeedbackR 29 = 5 := by
  norm_num [tableFeedbackR]

theorem tableGainR_bounds {n : ℕ} (hn : n ≤ 29) :
    tableFeedbackR n ∈ Icc (1 : ℝ) 5 := by
  constructor
  · rw [← tableFeedbackR_first]
    exact tableFeedbackR_monotone (Nat.zero_le n)
  · rw [← tableGainR_last]
    exact tableFeedbackR_monotone hn

theorem tableGainR_tail_bounds {n : ℕ} (hn : 9 ≤ n) (hn29 : n ≤ 29) :
    tableFeedbackR n ∈ Icc (3 : ℝ) 5 := by
  constructor
  · rw [← tableFeedbackR_last]
    exact tableFeedbackR_monotone hn
  · exact (tableGainR_bounds hn29).2

noncomputable def tableGainE : Matrix (Fin 29) (Fin 9) ℝ :=
  fun i j => if hi : i.val < 9 then
    if (⟨i.val, hi⟩ : Fin 9) = j then 1 else 0
  else tableGainL (tableFeedbackR (i.val + 1)) j

theorem tableGainE_nonneg (i : Fin 29) (j : Fin 9) :
    0 ≤ tableGainE i j := by
  by_cases hi : i.val < 9
  · simp only [tableGainE, dif_pos hi]
    split_ifs <;> norm_num
  · rw [tableGainE, dif_neg hi]
    have hb := tableGainR_tail_bounds (n := i.val + 1) (by omega) (by omega)
    exact tableGainL_nonneg hb.1 hb.2 j

theorem tableGain_actual_upper_endpoints {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (i : Fin 29) :
    (tableGainE *ᵥ tableFeedbackActualVector δ) i ≤
      wuImprovementLimit true δ (tableFeedbackR (i.val + 1)) := by
  by_cases hi : i.val < 9
  · change (∑ j : Fin 9, tableGainE i j * tableFeedbackActualVector δ j) ≤ _
    simp [tableGainE, hi, tableFeedbackActualVector]
  · have hb := tableGainR_tail_bounds (n := i.val + 1) (by omega) (by omega)
    have htail := tableGain_actual_upper_tail hδ hδhi hb.1 hb.2
    simpa only [Matrix.mulVec, dotProduct, tableGainE, dif_neg hi] using htail

end Wu2008DoubleSieve
