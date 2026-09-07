import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticPrimitives

open Set MeasureTheory Finset
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- Fixed odd-log expansion; the order is fixed before endpoint arithmetic. -/
def logLower (r : ℝ) : ℝ :=
  2 * ∑ i ∈ range 32, ((r-1)/(r+1))^(2*i+1)/((2*i+1 : ℕ) : ℝ)
def logUpper (r : ℝ) : ℝ :=
  logLower r + 2 * ((r-1)/(r+1))^65 / (1-((r-1)/(r+1))^2)

theorem log_bounds {r : ℝ} (hr : 1 ≤ r) :
    logLower r ≤ Real.log r ∧ Real.log r ≤ logUpper r := by
  have hp : 0 < r+1 := by linarith
  have h0 : 0 ≤ (r-1)/(r+1) := div_nonneg (by linarith) hp.le
  have h1 : (r-1)/(r+1) < 1 := (div_lt_one hp).2 (by linarith)
  have he : (1+(r-1)/(r+1))/(1-(r-1)/(r+1)) = r := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div h0 h1 32
  have hu := Real.log_div_le_sum_range_add h0 h1 32
  rw [he] at hl hu
  constructor
  · unfold logLower
    push_cast
    linarith
  · unfold logUpper logLower
    push_cast
    norm_num only at hu
    rw [mul_div_assoc]
    linarith

theorem scaled_log_bounds {r : ℝ} (hr : 1 ≤ r) (m : ℕ) :
    logLower r - m*logUpper 2 ≤ Real.log (r/2^m) ∧
    Real.log (r/2^m) ≤ logUpper r - m*logLower 2 := by
  have h := log_bounds hr
  have h2 := log_bounds (by norm_num : (1:ℝ) ≤ 2)
  rw [Real.log_div (by linarith : r ≠ 0) (by positivity), Real.log_pow]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2.2 (Nat.cast_nonneg (α := ℝ) m)]
  · nlinarith [mul_le_mul_of_nonneg_left h2.1 (Nat.cast_nonneg (α := ℝ) m)]

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
