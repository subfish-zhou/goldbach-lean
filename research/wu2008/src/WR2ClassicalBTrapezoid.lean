import WR2ClassicalBPrefix
import WR2ClassicalTrapezoid

noncomputable section
namespace WuPaper.ClassicalB
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

def splitUpper (u : ℝ) : ℝ := ClassicalLogSplit.upper 1 (u-1)/u

theorem left_le_splitUpper {u : ℝ} (hu : 2 ≤ u) : ClassicalC.left u ≤ splitUpper u := by
  exact div_le_div_of_nonneg_right (ClassicalLogSplit.bounds 1 (by linarith : 1 ≤ u-1)).2.2
    (by linarith)

/-- Endpoint-table version for sharing the grid with the C and D recurrences. -/
theorem table_upper {n : ℕ} {grid q U : ℕ → ℝ}
    (hgrid0 : grid 0 = 2) (hU0 : U 0 = 0)
    (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hgrid : ∀ i ≤ n, grid i ∈ Icc (2:ℝ) 5)
    (hq : ∀ i ≤ n, ClassicalC.left (grid i) ≤ q i)
    (hpay : ∀ i < n, (grid (i+1)-grid i)*(q i+q (i+1))/2+
      2*(grid (i+1)-grid i)^3/6 ≤ U (i+1)-U i) :
    B (grid n+1) ≤ U n := by
  have hsub (i : ℕ) (hi : i < n) {u : ℝ} (hu : u ∈ Icc (grid i) (grid (i+1))) :
      u ∈ Icc (2:ℝ) 5 :=
    ⟨(hgrid i (by omega)).1.trans hu.1,hu.2.trans (hgrid (i+1) (by omega)).2⟩
  have he := ClassicalTrapezoid.cumulative_upper hU0 hstep
    (fun i hi u hu => ClassicalC.left_deriv (hsub i hi hu).1)
    (fun i hi u hu => ClassicalC.leftD1_deriv (hsub i hi hu).1)
    (fun i hi u hu => (ClassicalC.left_bounds (hsub i hi hu).1 (hsub i hi hu).2).2.2.2)
    hq hpay
  rw [B_literal (by linarith [(hgrid n le_rfl).1])]
  simpa only [hgrid0,add_sub_cancel_right,ClassicalC.left] using he

end WuPaper.ClassicalB
#print axioms WuPaper.ClassicalB.table_upper
