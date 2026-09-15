import NodeGrid

namespace NodeExtension
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval BigOperators

/-- A constant endpoint lower bound integrates to its exact logarithmic weight. -/
theorem constant_log_lower {δ a b c : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 5)
    (hc : ∀ t ∈ Icc a b, c ≤ wuImprovementLimit true δ t) :
    c * log (b / a) ≤ ∫ t in a..b, wuImprovementLimit true δ t / t := by
  have hp : 0 < a := by linarith
  have hbpos : 0 < b := hp.trans_le hab
  have hlo : IntervalIntegrable (fun t : ℝ => c * (1 / t)) volume a b :=
    ((reciprocal_continuous hp hab).intervalIntegrable).const_mul c
  have hhi := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) ha hab (by linarith : b ≤ 10)
  have hm := intervalIntegral.integral_mono_on hab hlo hhi (fun t ht => by
    simpa only [mul_one_div] using div_le_div_of_nonneg_right (hc t ht)
      (by linarith [ht.1] : 0 ≤ t))
  rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hp hbpos] at hm
  exact hm

theorem grid_cell_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {i : ℕ} (hi : 3 ≤ i) (hi29 : i ≤ 29) :
    extendedNode (actualNine δ) i * log (rNode i / rNode (i - 1)) ≤
      ∫ t in rNode (i - 1)..rNode i, wuImprovementLimit true δ t / t := by
  have hl := rNode_bounds (show i - 1 ≤ 29 by omega)
  have hr := rNode_bounds hi29
  apply constant_log_lower hd hdhi hl.1 (rNode_mono (by omega)) hr.2
  intro t ht
  exact (extendedNode_le_actual hd hdhi (by omega) hi29).trans
    (wuImprovementLimit_upper_antitone hd hdhi
      ⟨hl.1.trans ht.1, ht.2.trans (hr.2.trans (by norm_num))⟩
      ⟨hr.1, hr.2.trans (by norm_num)⟩ ht.2)

/-- For later nodes this segment is empty; H(2.2) is never used at a larger point. -/
theorem initial_segment_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : 1 ≤ j) (hj21 : j ≤ 21) :
    actualNine δ 0 * log (rNode (gridStart j) / (rNode j - 1)) ≤
      ∫ t in (rNode j - 1)..rNode (gridStart j), wuImprovementLimit true δ t / t := by
  by_cases hlate : 12 ≤ j
  · rw [start_log_zero hlate, start_degenerate hlate]
    simp
  · have hs : gridStart j = 2 := by unfold gridStart; omega
    have hb := start_bounds hj hj21
    apply constant_log_lower hd hdhi hb.2.2.1 hb.2.2.2
      ((rNode_bounds (by omega : gridStart j ≤ 29)).2)
    intro t ht
    have htup : t ≤ upperNode 0 := by
      rw [hs] at ht
      norm_num [rNode, upperNode] at ht ⊢
      exact ht.2
    exact wuImprovementLimit_upper_antitone hd hdhi
      ⟨hb.2.2.1.trans ht.1, htup.trans ((upperNode_bounds 0).2.trans (by norm_num))⟩
      ⟨(upperNode_bounds 0).1, (upperNode_bounds 0).2.trans (by norm_num)⟩ htup

/-- Finite concatenation and the nonnegative [4.9,5] truncation. -/
theorem actual_twentyone_nat {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : 1 ≤ j) (hj21 : j ≤ 21) :
    originalTransfer (actualNine δ) j ≤ wuImprovementLimit false δ (rNode j) := by
  let f : ℝ → ℝ := fun t => wuImprovementLimit true δ t / t
  have hb := start_bounds hj hj21
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
  have hfirst := initial_segment_lower hd hdhi hj hj21
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ hb.2.2.1 hb.2.2.2 hsb.2)
    (hi _ _ hsb.1 (rNode_mono hs29) hr.2)
  have hlow : originalTransfer (actualNine δ) j ≤ ∫ t in (rNode j - 1)..rNode 29, f t := by
    unfold originalTransfer
    rw [← grid_start_index]
    exact (add_le_add hfirst hm).trans_eq hjoin
  have htail : 0 ≤ ∫ t in rNode 29..5, f t := by
    apply intervalIntegral.integral_nonneg hr.2
    intro t ht
    exact div_nonneg
      (wuImprovementLimit_nonneg true hd (by linarith : δ < 1 / 2)
        (hr.1.trans ht.1) (ht.2.trans (by norm_num))) (by linarith [ht.1, hr.1])
  have hj29 : rNode j - 1 ≤ rNode 29 := hb.2.2.2.trans (rNode_mono hs29)
  have hjoin5 := intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ hb.2.2.1 hj29 hr.2) (hi _ _ hr.1 hr.2 le_rfl)
  have hcross := wuImprovementLimit_lower_cross hd hdhi (s := rNode j) (t := 6)
    (by have hh := Nat.cast_nonneg (α := ℝ) j; dsimp [rNode]; linarith)
    ((rNode_bounds (by omega : j ≤ 29)).2.trans (by norm_num)) (by norm_num)
  have hn := wuImprovementLimit_nonneg false hd (by linarith : δ < 1 / 2)
    (s := 6) (by norm_num) (by norm_num)
  norm_num at hcross
  dsimp [f] at hlow htail hjoin5
  linarith

/-- Wu08 (3.11), for all twenty-one nodes and every admissible delta; no table premise. -/
theorem actual_twentyone {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) (j : Fin 21) :
    actualNine δ 0 * log (rNode (max 2 (j.val + 1 - 10)) / (rNode (j.val + 1) - 1)) +
      (∑ i ∈ Finset.Icc (max 3 (j.val + 1 - 9)) 29,
        extendedNode (actualNine δ) i * log (rNode i / rNode (i - 1))) ≤
      wuImprovementLimit false δ (rNode (j.val + 1)) :=
  actual_twentyone_nat hd hdhi (by omega) (by omega)

theorem originalTransfer_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {j : ℕ} (hj : 1 ≤ j) (hj21 : j ≤ 21) : 0 ≤ originalTransfer z j := by
  have hb := start_bounds hj hj21
  apply add_nonneg
  · apply mul_nonneg (hz 0)
    exact log_nonneg ((le_div_iff₀ (by linarith [hb.2.2.1] : 0 < rNode j - 1)).2
      (by simpa only [one_mul, gridStart] using hb.2.2.2))
  · apply Finset.sum_nonneg
    intro i hit
    have hh := Finset.mem_Icc.mp hit
    apply mul_nonneg (extendedNode_nonneg hz (by omega) hh.2)
    exact log_nonneg ((le_div_iff₀ (rNode_pos (i - 1))).2
      (by simpa only [one_mul] using rNode_mono (show i - 1 ≤ i by omega)))

end NodeExtension
