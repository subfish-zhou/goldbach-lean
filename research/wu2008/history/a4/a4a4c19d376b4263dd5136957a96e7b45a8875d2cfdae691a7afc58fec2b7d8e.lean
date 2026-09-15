import W01ContinuousNodes

namespace WuSource.SrcGrid
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open scoped Interval BigOperators

theorem start_bounds_all {j : ℕ} (hj : j ≤ 29) :
    2 ≤ gridStart j ∧ gridStart j ≤ 19 ∧
      1 ≤ rNode j - 1 ∧ rNode j - 1 ≤ rNode (gridStart j) := by
  have hs : 2 ≤ gridStart j ∧ gridStart j ≤ 19 := by
    unfold gridStart
    omega
  refine ⟨hs.1, hs.2, ?_, ?_⟩
  · have hn := Nat.cast_nonneg (α := ℝ) j
    dsimp [rNode]
    linarith
  · by_cases hlate : 12 ≤ j
    · exact (start_degenerate hlate).ge
    · have he : gridStart j = 2 := by unfold gridStart; omega
      have hn : (j : ℝ) ≤ 12 := by exact_mod_cast (show j ≤ 12 by omega)
      rw [he]
      dsimp [rNode]
      norm_num
      linarith

theorem initial_segment_lower_all {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : j ≤ 29) :
    actualNine δ 0 * log (rNode (gridStart j) / (rNode j - 1)) ≤
      ∫ t in (rNode j - 1)..rNode (gridStart j),
        wuImprovementLimit true δ t / t := by
  by_cases hlate : 12 ≤ j
  · rw [start_log_zero hlate, start_degenerate hlate]
    simp
  · by_cases hpos : 1 ≤ j
    · exact initial_segment_lower hd hdhi hpos (by omega)
    · have hj0 : j = 0 := by omega
      subst j
      have hb := start_bounds_all (j := 0) (by omega)
      apply constant_log_lower hd hdhi hb.2.2.1 hb.2.2.2
        (rNode_bounds (by norm_num [gridStart] : gridStart 0 ≤ 29)).2
      intro t ht
      have htup : t ≤ upperNode 0 := by
        norm_num [gridStart, rNode, upperNode] at ht ⊢
        exact ht.2
      exact wuImprovementLimit_upper_antitone hd hdhi
        ⟨hb.2.2.1.trans ht.1, htup.trans ((upperNode_bounds 0).2.trans (by norm_num))⟩
        ⟨(upperNode_bounds 0).1, (upperNode_bounds 0).2.trans (by norm_num)⟩ htup

theorem actual_tail_nonneg {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) :
    0 ≤ ∫ t in rNode 29..5, wuImprovementLimit true δ t / t := by
  have hr := rNode_bounds (i := 29) le_rfl
  apply intervalIntegral.integral_nonneg hr.2
  intro t ht
  exact div_nonneg
    (wuImprovementLimit_nonneg true hd (by linarith : δ < 1 / 2)
      (hr.1.trans ht.1) (ht.2.trans (by norm_num)))
    (by linarith [ht.1, hr.1])

theorem actual_integral_lower_all {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : j ≤ 29) :
    (∫ t in (rNode j - 1)..5, wuImprovementLimit true δ t / t) ≤
      wuImprovementLimit false δ (rNode j) := by
  have hc := wuImprovementLimit_lower_cross hd hdhi (s := rNode j) (t := 6)
    (by have hn := Nat.cast_nonneg (α := ℝ) j; dsimp [rNode]; linarith)
    ((rNode_bounds hj).2.trans (by norm_num)) (by norm_num)
  have hn := wuImprovementLimit_nonneg false hd (by linarith : δ < 1 / 2)
    (s := 6) (by norm_num) (by norm_num)
  norm_num at hc
  linarith

/-- The old 1..21 producer is reused; only the omitted indices need concatenation. -/
theorem actual_all_nat {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : j ≤ 29) :
    originalTransfer (actualNine δ) j ≤ wuImprovementLimit false δ (rNode j) := by
  by_cases hold : 1 ≤ j ∧ j ≤ 21
  · exact actual_twentyone_nat hd hdhi hold.1 hold.2
  · let f : ℝ → ℝ := fun t => wuImprovementLimit true δ t / t
    have hb := start_bounds_all hj
    have hs29 : gridStart j ≤ 29 := by omega
    have hr := rNode_bounds (i := 29) le_rfl
    have hsb := rNode_bounds hs29
    have hi (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hb5 : b ≤ 5) :
        IntervalIntegrable f volume a b :=
      wuImprovementLimit_div_intervalIntegrable true hd (by linarith : δ < 1 / 2)
        ha hab (by linarith)
    have hsum := grid_integral_sum (f := f) hs29
      (fun i hai hin => hi _ _ hsb.1 (rNode_mono hai) (rNode_bounds hin).2)
    have hm : (∑ i ∈ Finset.Icc (gridStart j + 1) 29,
        extendedNode (actualNine δ) i * log (rNode i / rNode (i - 1))) ≤
          ∫ t in rNode (gridStart j)..rNode 29, f t := by
      rw [← hsum]
      apply Finset.sum_le_sum
      intro i hit
      have hh := Finset.mem_Icc.mp hit
      exact grid_cell_lower hd hdhi (by omega) hh.2
    have hfirst := initial_segment_lower_all hd hdhi hj
    have hjoin := intervalIntegral.integral_add_adjacent_intervals
      (hi _ _ hb.2.2.1 hb.2.2.2 hsb.2)
      (hi _ _ hsb.1 (rNode_mono hs29) hr.2)
    have hlow : originalTransfer (actualNine δ) j ≤
        ∫ t in (rNode j - 1)..rNode 29, f t := by
      unfold originalTransfer
      rw [← grid_start_index]
      exact (add_le_add hfirst hm).trans_eq hjoin
    have hjoin5 := intervalIntegral.integral_add_adjacent_intervals
      (hi _ _ hb.2.2.1 (hb.2.2.2.trans (rNode_mono hs29)) hr.2)
      (hi _ _ hr.1 hr.2 le_rfl)
    have htail := actual_tail_nonneg hd hdhi
    have hcross := actual_integral_lower_all hd hdhi hj
    dsimp [f] at hlow hjoin5
    linarith

theorem actual_all {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) (j : Fin 30) :
    originalTransfer (actualNine δ) j.val ≤
      wuImprovementLimit false δ (rNode j.val) :=
  actual_all_nat hd hdhi (by omega)

theorem upperProfile_initial_integral_all (z : Fin 9 → ℝ) {j : ℕ} (hj : j ≤ 29) :
    (∫ t in (rNode j - 1)..rNode (gridStart j),
      WuTarget.W01Continuous.upperProfile z t / t) =
        z 0 * log (rNode (gridStart j) / (rNode j - 1)) := by
  by_cases hlate : 12 ≤ j
  · rw [start_log_zero hlate, start_degenerate hlate]
    simp
  · by_cases hpos : 1 ≤ j
    · exact WuTarget.W01Continuous.upperProfile_initial_integral z hpos (by omega)
    · have hs : gridStart j = 2 := by unfold gridStart; omega
      have hb := start_bounds_all hj
      have he : (∫ t in (rNode j - 1)..rNode (gridStart j),
          WuTarget.W01Continuous.upperProfile z t / t) =
            ∫ t in (rNode j - 1)..rNode (gridStart j), z 0 * (1 / t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hb.2.2.2] at ht
        dsimp only
        rw [WuTarget.W01Continuous.upperProfile_initial z
          ⟨hb.2.2.1.trans ht.1, by simpa only [hs] using ht.2⟩]
        ring
      rw [he, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos (by linarith [hb.2.2.1]) (rNode_pos _)]

/-- Exact equality to the already defined half-open staircase, including j = 0. -/
theorem hContinuous_node_all (z : Fin 9 → ℝ) {j : ℕ} (hj : j ≤ 29) :
    WuTarget.W01Continuous.hContinuous z (rNode j) = originalTransfer z j := by
  by_cases hold : 1 ≤ j ∧ j ≤ 21
  · exact WuTarget.W01Continuous.hContinuous_node_nat z hold.1 hold.2
  · have hb := start_bounds_all hj
    have hi := WuTarget.W01Continuous.upperProfile_div_integrable z
    have hsum := grid_integral_sum (f := fun t => WuTarget.W01Continuous.upperProfile z t / t)
      (show gridStart j ≤ 29 by omega) (fun _ _ _ => hi.intervalIntegrable)
    have he : (∑ i ∈ Finset.Icc (gridStart j + 1) 29,
        ∫ t in rNode (i - 1)..rNode i, WuTarget.W01Continuous.upperProfile z t / t) =
          ∑ i ∈ Finset.Icc (gridStart j + 1) 29,
            extendedNode z i * log (rNode i / rNode (i - 1)) := by
      apply Finset.sum_congr rfl
      intro i hit
      have hh := Finset.mem_Icc.mp hit
      exact WuTarget.W01Continuous.upperProfile_cell_integral z (by omega) hh.2
    have hjoin := intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable (a := rNode j - 1) (b := rNode (gridStart j)))
      (hi.intervalIntegrable (a := rNode (gridStart j)) (b := rNode 29))
    rw [upperProfile_initial_integral_all z hj, ← hsum, he] at hjoin
    unfold WuTarget.W01Continuous.hContinuous originalTransfer
    rw [← grid_start_index]
    exact hjoin.symm

end WuSource.SrcGrid
