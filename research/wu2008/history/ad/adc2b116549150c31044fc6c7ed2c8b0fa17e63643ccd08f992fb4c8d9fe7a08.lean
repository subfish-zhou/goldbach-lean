import SrcSingleFourthSource

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Real Set MeasureTheory Finset
open scoped Interval BigOperators

def sourceNode (i : ℕ) : ℝ := 2 + (i : ℝ) / 10
def sourceWeight (a b : ℝ) : ℝ :=
  log (b * (1 - 2 * truncatedSixthLowerAlpha * a) /
    (a * (1 - 2 * truncatedSixthLowerAlpha * b)))
def sourceKernel (s : ℝ) : ℝ :=
  1 / (s * (1 - 2 * truncatedSixthLowerAlpha * s))
def fourthGrid (k : ℕ) : ℝ :=
  if k = 0 then 1327 / 400 else (33 + (k : ℝ)) / 10
def fourthNodeSum (H : ℕ → ℝ) : ℝ :=
  8 * ∑ k ∈ range 16,
    sourceWeight (fourthGrid k) (fourthGrid (k + 1)) * H (14 + k)

theorem source_kernel_continuous {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 49 / 10) :
    ContinuousOn sourceKernel (uIcc a b) := by
  apply continuousOn_const.div
    (continuousOn_id.mul (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
  intro s hs
  rw [uIcc_of_le hab] at hs
  have hs0 : 0 < s := ha.trans_le hs.1
  have hsmax := hs.2.trans hb
  have hden : 0 < 1 - 2 * truncatedSixthLowerAlpha * s := by
    norm_num [truncatedSixthLowerAlpha]
    linarith
  exact mul_ne_zero hs0.ne' hden.ne'

theorem source_kernel_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 49 / 10) :
    (∫ s in a..b, sourceKernel s) = sourceWeight a b := by
  let F : ℝ → ℝ := fun s => log s - log (1 - 2 * truncatedSixthLowerAlpha * s)
  have hden (s : ℝ) (hs : s ≤ 49 / 10) :
      0 < 1 - 2 * truncatedSixthLowerAlpha * s := by
    norm_num [truncatedSixthLowerAlpha]
    linarith
  have hderiv : ∀ s ∈ uIcc a b, HasDerivAt F (sourceKernel s) s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hs0 : s ≠ 0 := (ha.trans_le hs.1).ne'
    have hd := (hden s (hs.2.trans hb)).ne'
    have h := ((hasDerivAt_id s).log hs0).sub
      (((hasDerivAt_id s).const_mul (2 * truncatedSixthLowerAlpha)).const_sub 1 |>.log hd)
    convert h using 1
    dsimp [sourceKernel]
    field_simp
    <;> ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (source_kernel_continuous ha hab hb).intervalIntegrable
  rw [hftc]
  have hb0 := ha.trans_le hab
  have hda := hden a (hab.trans hb)
  have hdb := hden b hb
  dsimp [F, sourceWeight]
  rw [log_div (mul_pos hb0 hda).ne' (mul_pos ha hdb).ne',
    log_mul hb0.ne' hda.ne', log_mul ha.ne' hdb.ne']
  ring

theorem source_weight_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 49 / 10) : 0 ≤ sourceWeight a b := by
  rw [← source_kernel_integral ha hab hb]
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  have hsmax := hs.2.trans hb
  have hden : 0 ≤ 1 - 2 * truncatedSixthLowerAlpha * s := by
    norm_num [truncatedSixthLowerAlpha]
    linarith
  exact div_nonneg (by norm_num) (mul_nonneg (ha.le.trans hs.1) hden)

theorem fourth_grid_bounds {k : ℕ} (hk : k ≤ 16) :
    (1327 / 400 : ℝ) ≤ fourthGrid k ∧ fourthGrid k ≤ 49 / 10 := by
  by_cases hz : k = 0
  · subst k
    norm_num [fourthGrid]
  · have hlo : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hhi : (k : ℝ) ≤ 16 := by exact_mod_cast hk
    simp only [fourthGrid, if_neg hz]
    constructor <;> linarith

theorem fourth_grid_mono {k : ℕ} (hk : k < 16) :
    fourthGrid k ≤ fourthGrid (k + 1) := by
  by_cases hz : k = 0
  · subst k
    norm_num [fourthGrid]
  · simp only [fourthGrid, if_neg hz, Nat.add_eq_zero_iff, Nat.succ_ne_zero,
      and_false, if_false, Nat.cast_add, Nat.cast_one]
    linarith

theorem fourth_grid_source_node (k : ℕ) :
    fourthGrid (k + 1) = sourceNode (14 + k) := by
  simp [fourthGrid, sourceNode]
  ring

theorem fourth_first_weight :
    sourceWeight (fourthGrid 0) (fourthGrid 1) =
      log (2 * truncatedSixthLowerAlpha * sourceNode 14 /
        (1 - 2 * truncatedSixthLowerAlpha * sourceNode 14)) := by
  norm_num [sourceWeight, fourthGrid, sourceNode, truncatedSixthLowerAlpha]

theorem fourth_later_weight {k : ℕ} (hk : 1 ≤ k) :
    sourceWeight (fourthGrid k) (fourthGrid (k + 1)) =
      log (sourceNode (14 + k) * (1 - 2 * truncatedSixthLowerAlpha * sourceNode (13 + k)) /
        (sourceNode (13 + k) * (1 - 2 * truncatedSixthLowerAlpha * sourceNode (14 + k)))) := by
  have hk0 : k ≠ 0 := by omega
  rw [fourth_grid_source_node]
  have he : fourthGrid k = sourceNode (13 + k) := by
    simp [fourthGrid, hk0, sourceNode]
    ring
  rw [he]
  rfl

theorem fourth_cell_lower {δ z : ℝ} {k : ℕ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hk : k < 16)
    (hz : 0 ≤ z) (hzH : z ≤ wuImprovementLimit true δ (sourceNode (14 + k))) :
    2 * sourceWeight (fourthGrid k) (fourthGrid (k + 1)) * z ≤
      ∫ s in fourthGrid k..fourthGrid (k + 1), fourthKernel δ s := by
  have ha := fourth_grid_bounds (by omega : k ≤ 16)
  have hb := fourth_grid_bounds (by omega : k + 1 ≤ 16)
  have hab := fourth_grid_mono hk
  have hg := fourth_geometry hd.le hh
  have ha0 : 0 < fourthGrid k := by linarith [ha.1]
  have hi := ((source_kernel_continuous ha0 hab hb.2).intervalIntegrable).const_mul (2 * z)
  have hH := fourth_kernel_integrable hd hh (hg.2.1.trans ha.1) hab (hb.2.trans hg.2.2.1)
  have hm := intervalIntegral.integral_mono_on hab hi hH (fun s hs => by
    have hs0 : 0 < s := ha0.trans_le hs.1
    have hsmax := hs.2.trans hb.2
    have hpos : 0 < s * (levelExponent δ - truncatedSixthLowerAlpha * s) := by
      apply mul_pos hs0
      norm_num [levelExponent, truncatedSixthLowerAlpha]
      linarith
    have hpos0 : 0 < s * (1 - 2 * truncatedSixthLowerAlpha * s) := by
      apply mul_pos hs0
      norm_num [truncatedSixthLowerAlpha]
      linarith
    have harg : s ≤ sourceNode (14 + k) := by rwa [← fourth_grid_source_node]
    have hn : sourceNode (14 + k) ≤ (49 / 10 : ℝ) := by
      rwa [← fourth_grid_source_node]
    have hbound := wuImprovementLimit_upper_antitone hd (by linarith : δ ≤ 1 / 10)
      ⟨by linarith [ha.1, hs.1], by linarith⟩
      ⟨by rw [← fourth_grid_source_node]; linarith [hb.1], by linarith⟩ harg
    have hminor := hzH.trans hbound
    have hden : 2 * (s * (levelExponent δ - truncatedSixthLowerAlpha * s)) ≤
        s * (1 - 2 * truncatedSixthLowerAlpha * s) := by
      dsimp [levelExponent]
      nlinarith only [mul_nonneg hd.le hs0.le]
    have hcompare : 2 * z / (s * (1 - 2 * truncatedSixthLowerAlpha * s)) ≤
        z / (s * (levelExponent δ - truncatedSixthLowerAlpha * s)) := by
      apply (div_le_div_iff₀ hpos0 hpos).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hden hz]
    have hactual := div_le_div_of_nonneg_right hminor hpos.le
    simpa only [sourceKernel, fourthKernel, mul_one_div] using hcompare.trans hactual)
  rw [intervalIntegral.integral_const_mul, source_kernel_integral ha0 hab hb.2] at hm
  nlinarith only [hm]

theorem fourth_nodes_to_source {δ : ℝ} {H : ℕ → ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hH0 : ∀ i ∈ Icc 14 29, 0 ≤ H i)
    (hH : ∀ i ∈ Icc 14 29, H i ≤ wuImprovementLimit true δ (sourceNode i)) :
    fourthNodeSum H ≤ fourthSource δ := by
  have hg := fourth_geometry hd.le hh
  have hint : ∀ k < 16, IntervalIntegrable (fourthKernel δ) volume
      (fourthGrid k) (fourthGrid (k + 1)) := by
    intro k hk
    exact fourth_kernel_integrable hd hh
      (hg.2.1.trans (fourth_grid_bounds (by omega)).1) (fourth_grid_mono hk)
      ((fourth_grid_bounds (by omega)).2.trans hg.2.2.1)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hlow : (∑ k ∈ range 16,
      2 * sourceWeight (fourthGrid k) (fourthGrid (k + 1)) * H (14 + k)) ≤
        ∫ s in fourthGrid 0..fourthGrid 16, fourthKernel δ s := by
    rw [← hsum]
    apply sum_le_sum
    intro k hk
    have hk16 := mem_range.mp hk
    have hidx : 14 + k ∈ Icc 14 29 := mem_Icc.mpr ⟨by omega, by omega⟩
    exact fourth_cell_lower hd hh hk16 (hH0 _ hidx) (hH _ hidx)
  have hfour := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 4)
  have htrunc := fourth_truncated_le_source hd hh
  have hmain : fourthNodeSum H ≤
      4 * ∫ s in (1327 / 400 : ℝ)..(49 / 10), fourthKernel δ s := by
    simpa [fourthNodeSum, fourthGrid, mul_assoc, ← mul_sum] using hfour
  exact hmain.trans htrunc

#check @fourth_nodes_to_source
#check @fourth_first_weight
#check @fourth_later_weight
#print axioms source_kernel_integral
#print axioms fourth_nodes_to_source
end WuSource.SrcSingle
