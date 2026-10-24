import WR2ClassicalCWeighted

noncomputable section
namespace WuPaper.ClassicalDTable
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

/-- D consumes the already bounded C endpoints on exactly the same grid. -/
theorem table_upper {n : ℕ} {grid q U : ℕ → ℝ}
    (hgrid0 : grid 0 = 4) (hU0 : U 0 = 0)
    (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hgrid : ∀ i ≤ n, grid i ∈ Icc (4:ℝ) 6)
    (hq : ∀ i ≤ n, C (grid i)/grid i ≤ q i)
    (hpay : ∀ i < n, (grid (i+1)-grid i)*(q i+q (i+1))/2+
      1*(grid (i+1)-grid i)^3/6 ≤ U (i+1)-U i) :
    D (grid n+1) ≤ U n := by
  have hsub (i : ℕ) (hi : i < n) {u : ℝ} (hu : u ∈ Icc (grid i) (grid (i+1))) :
      u ∈ Icc (4:ℝ) 6 :=
    ⟨(hgrid i (by omega)).1.trans hu.1,hu.2.trans (hgrid (i+1) (by omega)).2⟩
  have he := ClassicalTrapezoid.cumulative_upper hU0 hstep
    (fun i hi u hu => ClassicalQuotient.value_deriv (by linarith [(hsub i hi hu).1])
      (ClassicalCWeighted.C_deriv (hsub i hi hu).1))
    (fun i hi u hu => ClassicalQuotient.first_deriv (by linarith [(hsub i hi hu).1])
      (ClassicalCWeighted.C_deriv (hsub i hi hu).1) (ClassicalCWeighted.first_deriv (hsub i hi hu).1))
    (fun i hi u hu => ClassicalCWeighted.weighted_second_bound (hsub i hi hu).1 (hsub i hi hu).2)
    hq hpay
  have hc : D (grid n+1) = ∫ u in grid 0..grid n, ClassicalQuotient.value C u := by
    simp only [D,add_sub_cancel_right,hgrid0]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (hgrid n le_rfl).1] at hu
    simp only [ClassicalQuotient.value,max_eq_right (show (1:ℝ) ≤ u by linarith [hu.1])]
  rw [hc]
  exact he

end WuPaper.ClassicalDTable
#print axioms WuPaper.ClassicalDTable.table_upper
