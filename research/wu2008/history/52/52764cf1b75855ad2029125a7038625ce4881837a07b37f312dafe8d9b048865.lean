import MathlibNt.Wu2008DoubleSieve.TableGainGrid

/-!
# Clipped logarithmic source cells

The clipped grid runs from s-1 to five. A right endpoint below s-1
collapses its entire cell, whose logarithmic weight is exactly zero.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

noncomputable def tableGainClip (s : ℝ) (n : ℕ) : ℝ :=
  max (s - 1) (tableFeedbackR n)

noncomputable def tableGainWeight (s : ℝ) (i : Fin 29) : ℝ :=
  log (tableGainClip s (i.val + 1) / tableGainClip s i.val)

theorem tableGainClip_monotone (s : ℝ) : Monotone (tableGainClip s) :=
  fun _ _ hab => max_le_max_left _ (tableFeedbackR_monotone hab)

theorem tableGainClip_pos (s : ℝ) (n : ℕ) : 0 < tableGainClip s n := by
  have hR : 1 ≤ tableFeedbackR n := by
    rw [← tableFeedbackR_first]
    exact tableFeedbackR_monotone (Nat.zero_le n)
  exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR).trans_le (le_max_right _ _)

theorem tableGainClip_first {s : ℝ} (hs : 2 ≤ s) :
    tableGainClip s 0 = s - 1 := by
  rw [tableGainClip, tableFeedbackR_first, max_eq_left (by linarith)]

theorem tableGainClip_last {s : ℝ} (hs6 : s ≤ 6) :
    tableGainClip s 29 = 5 := by
  rw [tableGainClip, tableGainR_last, max_eq_right (by linarith)]

theorem tableGainClip_bounds {s : ℝ} {n : ℕ} (hs6 : s ≤ 6) (hn : n ≤ 29) :
    s - 1 ≤ tableGainClip s n ∧ tableGainClip s n ≤ 5 :=
  ⟨le_max_left _ _, max_le (by linarith) (tableGainR_bounds hn).2⟩

theorem tableGainClip_cell_subset {s : ℝ} {k : ℕ}
    (hs6 : s ≤ 6) (hk : k < 29) :
    uIcc (tableGainClip s k) (tableGainClip s (k + 1)) ⊆ uIcc (s - 1) 5 := by
  rw [uIcc_of_le (tableGainClip_monotone s (Nat.le_succ k)),
    uIcc_of_le (by linarith : s - 1 ≤ 5)]
  intro x hx
  exact ⟨(tableGainClip_bounds hs6 (by omega : k ≤ 29)).1.trans hx.1,
    hx.2.trans (tableGainClip_bounds hs6 (by omega : k + 1 ≤ 29)).2⟩

theorem tableGainWeight_nonneg (s : ℝ) (i : Fin 29) :
    0 ≤ tableGainWeight s i := by
  apply Real.log_nonneg
  exact (le_div_iff₀ (tableGainClip_pos s i.val)).mpr (by
    simpa only [one_mul] using tableGainClip_monotone s (Nat.le_succ i.val))

theorem tableGainClip_collapse {s : ℝ} {k : ℕ}
    (hk : tableFeedbackR (k + 1) ≤ s - 1) :
    tableGainClip s k = s - 1 ∧ tableGainClip s (k + 1) = s - 1 := by
  exact ⟨max_eq_left ((tableFeedbackR_monotone (Nat.le_succ k)).trans hk),
    max_eq_left hk⟩

theorem tableGainWeight_collapse {s : ℝ} {i : Fin 29}
    (hi : tableFeedbackR (i.val + 1) ≤ s - 1) :
    tableGainWeight s i = 0 := by
  have hc := tableGainClip_collapse hi
  have hp := tableGainClip_pos s i.val
  rw [hc.1] at hp
  rw [tableGainWeight, hc.1, hc.2, div_self hp.ne', log_one]

theorem tableGainClip_reciprocal_intervalIntegrable (s : ℝ) (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => 1 / u) volume
      (tableGainClip s k) (tableGainClip s (k + 1)) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div continuousOn_id
  rw [uIcc_of_le (tableGainClip_monotone s (Nat.le_succ k))]
  intro u hu
  exact ((tableGainClip_pos s k).trans_le hu.1).ne'

theorem tableGainWeight_integral (s : ℝ) (i : Fin 29) :
    (∫ u in tableGainClip s i.val..tableGainClip s (i.val + 1), 1 / u) =
      tableGainWeight s i := by
  rw [integral_one_div_of_pos (tableGainClip_pos s i.val)
    (tableGainClip_pos s (i.val + 1))]
  rfl

end Wu2008DoubleSieve
