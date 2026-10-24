import WR2ClassicalMidpointPanels

noncomputable section
namespace WuPaper.ClassicalTrapezoid
open Real Set MeasureTheory Finset
open scoped Interval

/-- Endpoint payments keep every level of the sieve recurrence on the same grid.
The conservative error reuses the already checked midpoint and Taylor estimates. -/
theorem cell {f f' f'' : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hB : ∀ t ∈ Icc a b, |f'' t| ≤ B) :
    (b-a)*(f a+f b)/2-B*(b-a)^3/6 ≤ ∫ t in a..b, f t ∧
      (∫ t in a..b, f t) ≤ (b-a)*(f a+f b)/2+B*(b-a)^3/6 := by
  have hm : (a+b)/2 ∈ Icc a b := by constructor <;> linarith only [hab]
  have ha := WuSource.SrcFourEnclosure.taylor_two_sided hm (show a ∈ Icc a b from ⟨le_rfl,hab⟩) hf hf' hB
  have hb := WuSource.SrcFourEnclosure.taylor_two_sided hm (show b ∈ Icc a b from ⟨hab,le_rfl⟩) hf hf' hB
  have he : f ((a+b)/2)-B*(b-a)^2/8 ≤ (f a+f b)/2 ∧
      (f a+f b)/2 ≤ f ((a+b)/2)+B*(b-a)^2/8 := by
    constructor <;> nlinarith only [ha.1,ha.2,hb.1,hb.2]
  have hl := mul_le_mul_of_nonneg_left he.1 (sub_nonneg.mpr hab)
  have hu := mul_le_mul_of_nonneg_left he.2 (sub_nonneg.mpr hab)
  have hi := WuSource.SrcFourEnclosure.midpoint_cell hab hf hf' hB
  constructor <;> nlinarith only [hl,hu,hi.1,hi.2]

/-- Cumulative payments telescope; later recurrence levels consume the same endpoint table. -/
theorem cumulative_upper {n : ℕ} {grid q U : ℕ → ℝ} {f f' f'' : ℝ → ℝ} {B : ℝ}
    (h0 : U 0 = 0)
    (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hf : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), HasDerivAt f (f' t) t)
    (hf' : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), HasDerivAt f' (f'' t) t)
    (hB : ∀ i < n, ∀ t ∈ Icc (grid i) (grid (i+1)), |f'' t| ≤ B)
    (hq : ∀ i ≤ n, f (grid i) ≤ q i)
    (hpay : ∀ i < n, (grid (i+1)-grid i)*(q i+q (i+1))/2+
      B*(grid (i+1)-grid i)^3/6 ≤ U (i+1)-U i) :
    (∫ t in grid 0..grid n, f t) ≤ U n := by
  have hi (i : ℕ) (hin : i < n) : IntervalIntegrable f volume (grid i) (grid (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hstep i hin)]
    exact fun t ht => (hf i hin t ht).continuousAt.continuousWithinAt
  have hc (i : ℕ) (hin : i < n) :
      (∫ t in grid i..grid (i+1), f t) ≤ U (i+1)-U i := by
    have he := (cell (hstep i hin) (hf i hin) (hf' i hin) (hB i hin)).2
    have hq' := mul_le_mul_of_nonneg_left
      (add_le_add (hq i (by omega)) (hq (i+1) (by omega)))
      (sub_nonneg.mpr (hstep i hin))
    linarith only [he,hq',hpay i hin]
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  have hsum := sum_le_sum (fun i hi => hc i (mem_range.mp hi))
  simpa only [sum_range_sub,h0,sub_zero] using hsum

end WuPaper.ClassicalTrapezoid
#print axioms WuPaper.ClassicalTrapezoid.cell

#print axioms WuPaper.ClassicalTrapezoid.cumulative_upper
