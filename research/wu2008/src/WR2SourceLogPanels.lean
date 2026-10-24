import WR2SourceLogCell
import WR2SourceLogLower

noncomputable section
namespace WuPaper.SourceLogChord
open Real Set MeasureTheory Finset
open scoped Interval

/-- A finite rational grid bounds the whole tail; no sampled-value premise. -/
theorem panels_le_integral {n : ℕ} {x L : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hx : ∀ i ≤ n, 0 < x i)
    (hstep : ∀ i < n, x i < x (i+1))
    (hL0 : ∀ i ≤ n, 0 ≤ L i)
    (hL : ∀ i ≤ n, L i ≤ log ((x i+1)/c)) :
    (∑ i ∈ range n, cell (x i) (x (i+1)) (L i) (L (i+1))) ≤
      ∫ t in x 0..x n, log ((t+1)/c)/t := by
  have hi (i : ℕ) (hin : i < n) :
      IntervalIntegrable (fun t => log ((t+1)/c)/t) volume (x i) (x (i+1)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := (hstep i hin).le)
    intro t ht
    have ht0 : 0 < t := (hx i (by omega)).trans_le ht.1
    fun_prop (disch := positivity)
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply sum_le_sum
  intro i him
  have hin := mem_range.mp him
  exact cell_le_integral (hx i (by omega)) (hstep i hin) hc
    (hL0 i (by omega)) (hL0 (i+1) (by omega))
    (hL i (by omega)) (hL (i+1) (by omega))

/-- The fixed logarithm polynomial makes every endpoint payment rational. -/
theorem rational_panels_le_integral {n : ℕ} {x : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hx : ∀ i ≤ n, 0 < x i)
    (hstep : ∀ i < n, x i < x (i+1)) (hcells : ∀ i ≤ n, c ≤ x i+1) :
    (∑ i ∈ range n, cell (x i) (x (i+1))
      (SourceLogRational.lower ((x i+1)/c))
      (SourceLogRational.lower ((x (i+1)+1)/c))) ≤
      ∫ t in x 0..x n, log ((t+1)/c)/t := by
  apply panels_le_integral hc hx hstep
  · intro i hi
    exact SourceLogRational.lower_nonneg ((one_le_div hc).mpr (hcells i hi))
  · intro i hi
    exact SourceLogRational.lower_le_log ((one_le_div hc).mpr (hcells i hi))

end WuPaper.SourceLogChord
#print axioms WuPaper.SourceLogChord.rational_panels_le_integral
