import WRMapMSigmaKernel
import WSrcGridTables

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve WuSource.SrcGrid
open scoped Interval BigOperators

def hGridExpression (Y : ℕ → ℝ) (j : ℕ) : ℝ :=
  Y 2 * log (rNode (max 2 (j - 10)) / (rNode j - 1)) +
    ∑ i ∈ Finset.Icc (max 3 (j - 9)) 29,
      Y i * log (rNode i / rNode (i - 1))

theorem hGridExpression_mono {Y Z : ℕ → ℝ}
    (hYZ : ∀ i, 2 ≤ i → i ≤ 29 → Y i ≤ Z i) {j : ℕ} (hj : j ≤ 29) :
    hGridExpression Y j ≤ hGridExpression Z j := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (hYZ 2 le_rfl (by omega))
      (initial_log_nonneg_all hj)
  · apply Finset.sum_le_sum
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    exact mul_le_mul_of_nonneg_right (hYZ i (by omega) hb.2) (cell_log_nonneg i)

theorem actual_H_cell_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {i : ℕ} (hi : 3 ≤ i) (hi29 : i ≤ 29) :
    wuImprovementLimit true δ (rNode i) * log (rNode i / rNode (i - 1)) ≤
      ∫ t in rNode (i - 1)..rNode i, wuImprovementLimit true δ t / t := by
  have hl := rNode_bounds (show i - 1 ≤ 29 by omega)
  have hr := rNode_bounds hi29
  apply constant_log_lower hd hdhi hl.1 (rNode_mono (by omega)) hr.2
  intro t ht
  exact wuImprovementLimit_upper_antitone hd hdhi
    ⟨hl.1.trans ht.1, ht.2.trans (hr.2.trans (by norm_num))⟩
    ⟨hr.1, hr.2.trans (by norm_num)⟩ ht.2

theorem hGridExpression_le_integral {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : j ≤ 29) :
    hGridExpression (fun i => wuImprovementLimit true δ (rNode i)) j ≤
      ∫ t in (rNode j - 1)..5, wuImprovementLimit true δ t / t := by
  let f : ℝ → ℝ := fun t => wuImprovementLimit true δ t / t
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
      wuImprovementLimit true δ (rNode i) * log (rNode i / rNode (i - 1))) ≤
        ∫ t in rNode (gridStart j)..rNode 29, f t := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro i hit
    have hh := Finset.mem_Icc.mp hit
    exact actual_H_cell_lower hd hdhi (by omega) hh.2
  have hfirst := initial_segment_lower_all hd hdhi hj
  have hn : actualNine δ 0 = wuImprovementLimit true δ (rNode 2) := by
    change wuImprovementLimit true δ (upperNode 0) = _
    exact congrArg (wuImprovementLimit true δ) (by norm_num [upperNode, rNode])
  rw [hn] at hfirst
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ hb.2.2.1 hb.2.2.2 hsb.2)
    (hi _ _ hsb.1 (rNode_mono hs29) hr.2)
  have hlow : hGridExpression (fun i => wuImprovementLimit true δ (rNode i)) j ≤
      ∫ t in (rNode j - 1)..rNode 29, f t := by
    unfold hGridExpression
    rw [← grid_start_index]
    exact (add_le_add hfirst hm).trans_eq hjoin
  have hjoin5 := intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ hb.2.2.1 (hb.2.2.2.trans (rNode_mono hs29)) hr.2)
    (hi _ _ hr.1 hr.2 le_rfl)
  have htail := actual_tail_nonneg hd hdhi
  dsimp [f] at hlow hjoin5
  linarith

theorem equation311 {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {j : ℕ} (hj : j ≤ 29) :
    wuImprovementLimit true δ (rNode 2) *
        log (rNode (max 2 (j - 10)) / (rNode j - 1)) +
      (∑ i ∈ Finset.Icc (max 3 (j - 9)) 29,
        wuImprovementLimit true δ (rNode i) * log (rNode i / rNode (i - 1))) ≤
      wuImprovementLimit false δ (rNode j) :=
  (hGridExpression_le_integral hd hdhi hj).trans (actual_integral_lower_all hd hdhi hj)

theorem equation311_input_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {Y : ℕ → ℝ} (hY : ∀ i, 2 ≤ i → i ≤ 29 →
      Y i ≤ wuImprovementLimit true δ (rNode i)) {j : ℕ} (hj : j ≤ 29) :
    hGridExpression Y j ≤ wuImprovementLimit false δ (rNode j) :=
  (hGridExpression_mono hY hj).trans (equation311 hd hdhi hj)

theorem hGridExpression_initial (Y : ℕ → ℝ) :
    hGridExpression Y 0 = Y 2 * log (rNode 2) +
      ∑ i ∈ Finset.Icc 3 29, Y i * log (rNode i / rNode (i - 1)) := by
  norm_num [hGridExpression, rNode]

theorem hGridExpression_late (Y : ℕ → ℝ) {j : ℕ} (hj : 12 ≤ j) :
    hGridExpression Y j =
      ∑ i ∈ Finset.Icc (max 3 (j - 9)) 29, Y i * log (rNode i / rNode (i - 1)) := by
  unfold hGridExpression
  change Y 2 * log (rNode (gridStart j) / (rNode j - 1)) + _ = _
  rw [start_log_zero hj, mul_zero, zero_add]

theorem hGridExpression_at12 (Y : ℕ → ℝ) :
    hGridExpression Y 12 =
      ∑ i ∈ Finset.Icc 3 29, Y i * log (rNode i / rNode (i - 1)) := by
  simpa using hGridExpression_late Y (j := 12) le_rfl

theorem hGridExpression_at29 (Y : ℕ → ℝ) :
    hGridExpression Y 29 =
      ∑ i ∈ Finset.Icc 20 29, Y i * log (rNode i / rNode (i - 1)) := by
  simpa using hGridExpression_late Y (j := 29) (by norm_num)

theorem equation311_uniform :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ j : Fin 30,
      hGridExpression (fun i => wuImprovementLimit true δ (rNode i)) j.val ≤
        wuImprovementLimit false δ (rNode j.val) :=
  fun _ hd hdhi j => equation311 hd hdhi (by omega)

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.hGridExpression
#check @WuPaper.RMapMSigma.hGridExpression_mono
#check @WuPaper.RMapMSigma.actual_H_cell_lower
#check @WuPaper.RMapMSigma.hGridExpression_le_integral
#check @WuPaper.RMapMSigma.equation311
#check @WuPaper.RMapMSigma.equation311_input_lower
#check @WuPaper.RMapMSigma.hGridExpression_initial
#check @WuPaper.RMapMSigma.hGridExpression_late
#check @WuPaper.RMapMSigma.hGridExpression_at12
#check @WuPaper.RMapMSigma.hGridExpression_at29
#check @WuPaper.RMapMSigma.equation311_uniform
#print axioms WuPaper.RMapMSigma.hGridExpression
#print axioms WuPaper.RMapMSigma.hGridExpression_mono
#print axioms WuPaper.RMapMSigma.actual_H_cell_lower
#print axioms WuPaper.RMapMSigma.hGridExpression_le_integral
#print axioms WuPaper.RMapMSigma.equation311
#print axioms WuPaper.RMapMSigma.equation311_input_lower
#print axioms WuPaper.RMapMSigma.hGridExpression_initial
#print axioms WuPaper.RMapMSigma.hGridExpression_late
#print axioms WuPaper.RMapMSigma.hGridExpression_at12
#print axioms WuPaper.RMapMSigma.hGridExpression_at29
#print axioms WuPaper.RMapMSigma.equation311_uniform
