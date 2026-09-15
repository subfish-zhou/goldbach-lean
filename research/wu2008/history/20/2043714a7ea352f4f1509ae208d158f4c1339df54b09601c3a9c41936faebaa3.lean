import RMapMFifthClassical

namespace WuPaper.RMapMFifth
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open WuTarget.Wu08FifthSource WuSource.SrcFifthGain
open scoped Interval
noncomputable section

theorem cross_cell_error {qLower qUpper eLower eUpper : ℝ}
    (hl : |(∫ s in node 20..geometricSplit, lowerWeight s)-qLower| ≤ eLower)
    (hu : |(∫ s in geometricSplit..node 21, upperWeight s)-qUpper| ≤ eUpper) :
    |cellWeight 6-(qLower+qUpper)| ≤ eLower+eUpper := by
  rw [cell_weight_cross]
  apply abs_le.mpr
  rcases abs_le.mp hl with ⟨hll, hlu⟩
  rcases abs_le.mp hu with ⟨hul, huu⟩
  constructor <;> linarith only [hll, hlu, hul, huu]

theorem cell_weight_enclosure {j : ℕ} (hj : j < 13) {p : ℝ → ℝ} {q e rho : ℝ}
    (hp : IntervalIntegrable p volume (cellLower j) (cellUpper j))
    (herr : ∀ s ∈ Icc (cellLower j) (cellUpper j), |weight s-p s| ≤ e)
    (hquad : |(∫ s in cellLower j..cellUpper j, p s)-q| ≤ rho) :
    |cellWeight j-q| ≤ (cellUpper j-cellLower j)*e+rho := by
  have h := interval_error (cell_geometry hj).2.1 (cell_weight_integrable hj) hp herr
  change |cellWeight j-(∫ s in cellLower j..cellUpper j, p s)| ≤ _ at h
  apply abs_le.mpr
  rcases abs_le.mp h with ⟨hl, hu⟩
  rcases abs_le.mp hquad with ⟨hql, hqu⟩
  constructor <;> linarith only [hl, hu, hql, hqu]

theorem cell_weight_directed_enclosure {j : ℕ} (hj : j < 13)
    {p : ℝ → ℝ} {q e rho : ℝ}
    (hp : IntervalIntegrable p volume (cellLower j) (cellUpper j))
    (herr : ∀ s ∈ Icc (cellLower j) (cellUpper j), |weight s-p s| ≤ e)
    (hquad : |(∫ s in cellLower j..cellUpper j, p s)-q| ≤ rho) :
    q-rho-(cellUpper j-cellLower j)*e ≤ cellWeight j := by
  have h := cell_weight_enclosure hj hp herr hquad
  linarith [(abs_le.mp h).1]

theorem grid_error {h q e : ℕ → ℝ}
    (herr : ∀ j < 13, |cellWeight j-q j| ≤ e j) :
    |gridGain h-directedGain h q| ≤
      8*∑ j ∈ Finset.range 13, e j*|h (15+j)| := by
  have hs : |∑ j ∈ Finset.range 13, (cellWeight j-q j)*h (15+j)| ≤
      ∑ j ∈ Finset.range 13, e j*|h (15+j)| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (herr j (Finset.mem_range.mp hj)) (abs_nonneg _)
  have hid : gridGain h-directedGain h q =
      8*(∑ j ∈ Finset.range 13, (cellWeight j-q j)*h (15+j)) := by
    unfold gridGain directedGain
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

theorem gain_directed_enclosures {δ : ℝ} {h q e rho : ℕ → ℝ}
    {p : ℕ → ℝ → ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    (hp : ∀ j < 13, IntervalIntegrable (p j) volume (cellLower j) (cellUpper j))
    (herr : ∀ j < 13, ∀ s ∈ Icc (cellLower j) (cellUpper j),
      |weight s-p j s| ≤ e j)
    (hquad : ∀ j < 13, |(∫ s in cellLower j..cellUpper j, p j s)-q j| ≤ rho j) :
    (8*∑ j ∈ Finset.range 13,
      (q j-rho j-(cellUpper j-cellLower j)*e j)*h (15+j)) ≤
        sourceGain (wuImprovementLimit false δ) := by
  apply le_trans (b := gridGain h)
  · apply directed_gain_le_grid hn
    intro j hj
    exact cell_weight_directed_enclosure hj (hp j hj) (herr j hj) (hquad j hj)
  · exact grid_le_actual_source hδ hd hc

theorem gain_weight_error_lower {δ : ℝ} {h q e : ℕ → ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    (herr : ∀ j < 13, |cellWeight j-q j| ≤ e j) :
    (8*∑ j ∈ Finset.range 13, (q j-e j)*h (15+j)) ≤
      sourceGain (wuImprovementLimit false δ) := by
  apply le_trans (b := gridGain h)
  · apply directed_gain_le_grid hn
    intro j hj
    linarith [(abs_le.mp (herr j hj)).1]
  · exact grid_le_actual_source hδ hd hc

set_option pp.fullNames true
#check @cross_cell_error
#print axioms cross_cell_error
#check @cell_weight_enclosure
#print axioms cell_weight_enclosure
#check @cell_weight_directed_enclosure
#print axioms cell_weight_directed_enclosure
#check @grid_error
#print axioms grid_error
#check @gain_directed_enclosures
#print axioms gain_directed_enclosures
#check @gain_weight_error_lower
#print axioms gain_weight_error_lower

end
end WuPaper.RMapMFifth
