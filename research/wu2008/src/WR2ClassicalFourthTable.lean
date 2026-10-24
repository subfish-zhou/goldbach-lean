import WR2ClassicalFourthSplit

noncomputable section
namespace WuPaper.ClassicalFourth
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

theorem initial_deriv {s : ℝ} (hs : 3 ≤ s) :
    HasDerivAt initial (ClassicalB.firstValue s) s := (ClassicalB.B_deriv hs).const_add 1

theorem terminal_deriv {s : ℝ} (hs : 5 ≤ s) :
    HasDerivAt terminal (terminalD1 s) s :=
  ((ClassicalB.B_deriv (by linarith)).const_add 1).add (ClassicalD.D_deriv hs)

theorem terminalD1_deriv {s : ℝ} (hs : 5 ≤ s) :
    HasDerivAt terminalD1 (terminalD2 s) s :=
  (ClassicalB.deriv_deriv (by linarith)).add (ClassicalD.first_deriv hs)

/-- The outer table uses the same cumulative-payment interface as B,C,D. -/
theorem segment_upper {n : ℕ} {grid q U : ℕ → ℝ} {f f' f'' : ℝ → ℝ}
    (h0 : U 0 = 0) (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hgrid : ∀ i ≤ n, grid i ∈ Icc (3:ℝ) (R-1))
    (hf : ∀ i < n, ∀ s ∈ Icc (grid i) (grid (i+1)), HasDerivAt f (f' s) s)
    (hf' : ∀ i < n, ∀ s ∈ Icc (grid i) (grid (i+1)), HasDerivAt f' (f'' s) s)
    (hF : ∀ i < n, ∀ s ∈ Icc (grid i) (grid (i+1)), |f s| ≤ 8 ∧ |f' s| ≤ 3 ∧ |f'' s| ≤ 3)
    (hq : ∀ i ≤ n, kernel f (grid i) ≤ q i)
    (hpay : ∀ i < n, (grid (i+1)-grid i)*(q i+q (i+1))/2+
      56*(grid (i+1)-grid i)^3/6 ≤ U (i+1)-U i) :
    (∫ s in grid 0..grid n, kernel f s) ≤ U n := by
  have hsub (i : ℕ) (hi : i < n) {s : ℝ} (hs : s ∈ Icc (grid i) (grid (i+1))) :
      s ∈ Icc (3:ℝ) (R-1) :=
    ⟨(hgrid i (by omega)).1.trans hs.1,hs.2.trans (hgrid (i+1) (by omega)).2⟩
  exact ClassicalTrapezoid.cumulative_upper h0 hstep
    (fun i hi s hs => kernel_deriv (by linarith [(hsub i hi hs).1])
      (by linarith [(hsub i hi hs).2]) (hf i hi s hs))
    (fun i hi s hs => kernelD1_deriv (by linarith [(hsub i hi hs).1])
      (by linarith [(hsub i hi hs).2]) (hf i hi s hs) (hf' i hi s hs))
    (fun i hi s hs => kernel_second_bound (hsub i hi hs).1 (hsub i hi hs).2
      (hF i hi s hs).1 (hF i hi s hs).2.1 (hF i hi s hs).2.2)
    hq hpay

theorem initial_segment_upper {n : ℕ} {grid q U : ℕ → ℝ}
    (h0 : U 0 = 0) (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hgrid : ∀ i ≤ n, grid i ∈ Icc (3:ℝ) 5)
    (hq : ∀ i ≤ n, kernel initial (grid i) ≤ q i)
    (hpay : ∀ i < n, (grid (i+1)-grid i)*(q i+q (i+1))/2+
      56*(grid (i+1)-grid i)^3/6 ≤ U (i+1)-U i) :
    (∫ s in grid 0..grid n, kernel initial s) ≤ U n := by
  have hsub (i : ℕ) (hi : i < n) {s : ℝ} (hs : s ∈ Icc (grid i) (grid (i+1))) :
      s ∈ Icc (3:ℝ) 5 :=
    ⟨(hgrid i (by omega)).1.trans hs.1,hs.2.trans (hgrid (i+1) (by omega)).2⟩
  exact segment_upper h0 hstep
    (fun i hi => ⟨(hgrid i hi).1,(hgrid i hi).2.trans (by norm_num [R])⟩)
    (fun i hi s hs => initial_deriv (hsub i hi hs).1)
    (fun i hi s hs => ClassicalB.deriv_deriv (hsub i hi hs).1)
    (fun i hi s hs => initial_bounds (hsub i hi hs).1 (by linarith [(hsub i hi hs).2])) hq hpay

theorem terminal_segment_upper {n : ℕ} {grid q U : ℕ → ℝ}
    (h0 : U 0 = 0) (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hgrid : ∀ i ≤ n, grid i ∈ Icc (5:ℝ) (R-1))
    (hq : ∀ i ≤ n, kernel terminal (grid i) ≤ q i)
    (hpay : ∀ i < n, (grid (i+1)-grid i)*(q i+q (i+1))/2+
      56*(grid (i+1)-grid i)^3/6 ≤ U (i+1)-U i) :
    (∫ s in grid 0..grid n, kernel terminal s) ≤ U n := by
  have hsub (i : ℕ) (hi : i < n) {s : ℝ} (hs : s ∈ Icc (grid i) (grid (i+1))) :
      s ∈ Icc (5:ℝ) (R-1) :=
    ⟨(hgrid i (by omega)).1.trans hs.1,hs.2.trans (hgrid (i+1) (by omega)).2⟩
  exact segment_upper h0 hstep
    (fun i hi => ⟨by linarith [(hgrid i hi).1],(hgrid i hi).2⟩)
    (fun i hi s hs => terminal_deriv (hsub i hi hs).1)
    (fun i hi s hs => terminalD1_deriv (hsub i hi hs).1)
    (fun i hi s hs => terminal_bounds (hsub i hi hs).1
      ((hsub i hi hs).2.trans (by norm_num [R]))) hq hpay

end WuPaper.ClassicalFourth
#print axioms WuPaper.ClassicalFourth.initial_segment_upper
#print axioms WuPaper.ClassicalFourth.terminal_segment_upper
