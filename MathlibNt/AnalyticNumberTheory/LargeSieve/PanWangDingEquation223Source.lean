import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEquation223Contour

set_option maxHeartbeats 800000
noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Literal (2.15) abscissa. -/
def panSourceSigma (x : ℕ) : ℝ := 1 + 1 / Real.log x
/-- Literal (2.16) height. -/
def panSourceHeight (x : ℕ) : ℝ := Real.exp (2 * (Real.log x) ^ 2)

/-- Elementary telescoping majorant for the sum appearing in (2.23). -/
theorem panHalfSum_le (N : ℕ) : panHalfSum N ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp [panHalfSum]
  | succ N ih =>
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hNp : (0 : ℝ) < N + 1 := by positivity
    have ha := Real.sq_sqrt hN
    have hb := Real.sq_sqrt hNp.le
    have hab : Real.sqrt N ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hab0 := Real.sqrt_nonneg (N : ℝ)
    have hbp := Real.sqrt_pos.mpr hNp
    have hinv : (Real.sqrt ((N : ℝ) + 1))⁻¹ ≤
        2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) := by
      rw [inv_eq_one_div, div_le_iff₀ hbp]
      nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N)]
    rw [panHalfSum, Finset.sum_Icc_succ_top (by omega)]
    change panHalfSum N + (Real.sqrt (↑(N + 1) : ℝ))⁻¹ ≤ _
    push_cast
    linarith

theorem panSourceSigma_bounds {x : ℕ} (hx : 1 ≤ Real.log x) :
    1 / 2 ≤ panSourceSigma x ∧ panSourceSigma x ≤ 2 := by
  have hp : 0 < Real.log x := by linarith
  have hpos := one_div_pos.mpr hp
  have hle : 1 / Real.log x ≤ 1 := (div_le_one hp).mpr hx
  unfold panSourceSigma
  constructor <;> linarith


end AnalyticNumberTheory.LargeSieve