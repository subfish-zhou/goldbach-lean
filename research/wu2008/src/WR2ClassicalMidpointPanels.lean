import WSrcFourEnclosureQuadrature

noncomputable section
namespace WuPaper.ClassicalMidpoint
open Real Set MeasureTheory Finset
open scoped Interval

/-- A finite partition reuses the existing second-derivative midpoint estimate. -/
theorem panels_lower {n : ℕ} {L f f' f'' : ℝ → ℝ} {grid : ℕ → ℝ} {B : ℝ}
    (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hf : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), HasDerivAt f (f' t) t)
    (hf' : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), HasDerivAt f' (f'' t) t)
    (hB : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), |f'' t| ≤ B)
    (hL : ∀ i < n, L ((grid i+grid (i+1))/2) ≤ f ((grid i+grid (i+1))/2)) :
    (∑ i ∈ range n, ((grid (i+1)-grid i)*L ((grid i+grid (i+1))/2)-
      B*(grid (i+1)-grid i)^3/24)) ≤ ∫ t in grid 0..grid n, f t := by
  have hi (i : ℕ) (hin : i < n) : IntervalIntegrable f volume (grid i) (grid (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hstep i hin)]
    exact fun t ht => (hf i hin t ht).continuousAt.continuousWithinAt
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply sum_le_sum
  intro i him
  have hin := mem_range.mp him
  have hm := (WuSource.SrcFourEnclosure.midpoint_cell (hstep i hin)
    (hf i hin) (hf' i hin) (hB i hin)).1
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left (hL i hin)
    (sub_nonneg.mpr (hstep i hin))) _).trans hm

/-- Upper payments use the same partition and the same error bound. -/
theorem panels_upper {n : ℕ} {U f f' f'' : ℝ → ℝ} {grid : ℕ → ℝ} {B : ℝ}
    (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hf : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), HasDerivAt f (f' t) t)
    (hf' : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), HasDerivAt f' (f'' t) t)
    (hB : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), |f'' t| ≤ B)
    (hU : ∀ i < n, f ((grid i+grid (i+1))/2) ≤ U ((grid i+grid (i+1))/2)) :
    (∫ t in grid 0..grid n, f t) ≤
      ∑ i ∈ range n, ((grid (i+1)-grid i)*U ((grid i+grid (i+1))/2)+
        B*(grid (i+1)-grid i)^3/24) := by
  have hi (i : ℕ) (hin : i < n) : IntervalIntegrable f volume (grid i) (grid (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hstep i hin)]
    exact fun t ht => (hf i hin t ht).continuousAt.continuousWithinAt
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply sum_le_sum
  intro i him
  have hin := mem_range.mp him
  have hm := (WuSource.SrcFourEnclosure.midpoint_cell (hstep i hin)
    (hf i hin) (hf' i hin) (hB i hin)).2
  exact hm.trans (add_le_add_left (mul_le_mul_of_nonneg_left (hU i hin)
    (sub_nonneg.mpr (hstep i hin))) _)

end WuPaper.ClassicalMidpoint
#print axioms WuPaper.ClassicalMidpoint.panels_lower
#print axioms WuPaper.ClassicalMidpoint.panels_upper
