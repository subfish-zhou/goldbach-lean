import WR2ClassicalCBounds
import WR2ClassicalLogSplit
import WR2ClassicalMidpointPanels

noncomputable section
namespace WuPaper.ClassicalC
open Real Set MeasureTheory Wu08OriginalFirstSteps Finset
open scoped Interval

def lowerKernel (depth : ℕ) (s u : ℝ) : ℝ :=
  ClassicalLogSplit.lower depth (u-1)/u*ClassicalLogSplit.lower depth ((s-1)/(u+1))
def upperKernel (depth : ℕ) (s u : ℝ) : ℝ :=
  ClassicalLogSplit.upper depth (u-1)/u*ClassicalLogSplit.upper depth ((s-1)/(u+1))

theorem kernel_bounds (depth : ℕ) {s u : ℝ} (hu : 2 ≤ u) (hus : u ≤ s-2) :
    lowerKernel depth s u ≤ kernel s u ∧ kernel s u ≤ upperKernel depth s u := by
  have h0 : 0 < u := by linarith
  have hr : 1 ≤ (s-1)/(u+1) := (one_le_div (by linarith)).mpr (by linarith)
  obtain ⟨hL0,hL,hU⟩ := ClassicalLogSplit.bounds depth (show 1 ≤ u-1 by linarith)
  obtain ⟨hR0,hR,hV⟩ := ClassicalLogSplit.bounds depth hr
  have hlog : 0 ≤ log (u-1) := log_nonneg (by linarith)
  have hright : right s u = log ((s-1)/(u+1)) :=
    (log_div (by linarith : s-1 ≠ 0) (by linarith : u+1 ≠ 0)).symm
  unfold lowerKernel upperKernel kernel left
  rw [hright]
  constructor
  · exact mul_le_mul (div_le_div_of_nonneg_right hL h0.le) hR hR0 (div_nonneg hlog h0.le)
  · exact mul_le_mul (div_le_div_of_nonneg_right hU h0.le) hV (log_nonneg hr)
      (div_nonneg (hlog.trans hU) h0.le)

/-- Rational midpoint values enclose the original classical recurrence integral. -/
theorem C_enclosure {s : ℝ} (hs : 4 ≤ s) (hs7 : s ≤ 7)
    (depth n : ℕ) (grid : ℕ → ℝ)
    (h0 : grid 0 = 2) (hn : grid n = s-2)
    (hx : ∀ i ≤ n, grid i ∈ Set.Icc 2 (s-2))
    (hstep : ∀ i < n, grid i ≤ grid (i+1)) :
    (∑ i ∈ range n, ((grid (i+1)-grid i)*lowerKernel depth s ((grid i+grid (i+1))/2)-
      8*(grid (i+1)-grid i)^3/24)) ≤ C s ∧
    C s ≤ ∑ i ∈ range n, ((grid (i+1)-grid i)*upperKernel depth s ((grid i+grid (i+1))/2)+
      8*(grid (i+1)-grid i)^3/24) := by
  have hsub (i : ℕ) (hi : i < n) {t : ℝ} (ht : t ∈ Set.Icc (grid i) (grid (i+1))) :
      t ∈ Set.Icc 2 (s-2) := ⟨(hx i (by omega)).1.trans ht.1,ht.2.trans (hx (i+1) (by omega)).2⟩
  have hm (i : ℕ) (hi : i < n) : (grid i+grid (i+1))/2 ∈ Set.Icc 2 (s-2) := by
    apply hsub i hi
    constructor <;> linarith only [hstep i hi]
  have he : C s = ∫ t in grid 0..grid n, kernel s t := by
    rw [h0,hn,C_integral hs]
  rw [he]
  constructor
  · apply ClassicalMidpoint.panels_lower hstep
      (fun i hi t ht => kernel_deriv s (hsub i hi ht).1)
      (fun i hi t ht => kernelD1_deriv s (hsub i hi ht).1)
      (fun i hi t ht => kernelD2_bound hs7 (hsub i hi ht).1 (hsub i hi ht).2)
    exact fun i hi => (kernel_bounds depth (hm i hi).1 (hm i hi).2).1
  · apply ClassicalMidpoint.panels_upper hstep
      (fun i hi t ht => kernel_deriv s (hsub i hi ht).1)
      (fun i hi t ht => kernelD1_deriv s (hsub i hi ht).1)
      (fun i hi t ht => kernelD2_bound hs7 (hsub i hi ht).1 (hsub i hi ht).2)
    exact fun i hi => (kernel_bounds depth (hm i hi).1 (hm i hi).2).2

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.C_enclosure
