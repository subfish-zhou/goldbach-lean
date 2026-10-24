import WR2ClassicalCBounds
import WR2ClassicalMidpointPanels
import WR2ClassicalLogSplit

noncomputable section
namespace WuPaper.ClassicalB
open Real Set MeasureTheory Finset Wu08OriginalFirstSteps
open scoped Interval

def point (h : ℝ) (i : ℕ) : ℝ := 2+h*i
def upperValue (u : ℝ) : ℝ := WuSource.SrcFourEnclosure.logHi (u-1)/u

theorem upperValue_bounds {u : ℝ} (hu : 2 ≤ u) : ClassicalC.left u ≤ upperValue u := by
  exact div_le_div_of_nonneg_right
    (WuSource.SrcFourEnclosure.log_bounds (by linarith : 1 ≤ u-1)).2.2 (by linarith)

/-- Every prefix of a single certified midpoint table bounds B; no inner integral is recomputed. -/
theorem prefix_upper {h : ℝ} (hh : 0 ≤ h) (n : ℕ) (hn : h*n ≤ 3)
    (q : ℕ → ℝ) (hq : ∀ i < n, upperValue ((point h i+point h (i+1))/2) ≤ q i) :
    B (3+h*n) ≤ h*(∑ i ∈ range n, q i)+(n:ℝ)*2*h^3/24 := by
  have hwidth (i : ℕ) : point h (i+1)-point h i = h := by
    simp only [point,Nat.cast_add,Nat.cast_one]; ring
  have hstep (i : ℕ) (_hi : i < n) : point h i ≤ point h (i+1) := by
    linarith only [hwidth i,hh]
  have hsub (i : ℕ) (hi : i < n) {u : ℝ} (hu : u ∈ Icc (point h i) (point h (i+1))) :
      u ∈ Icc (2:ℝ) 5 := by
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hin : (i:ℝ)+1 ≤ n := by exact_mod_cast (show i+1 ≤ n by omega)
    have hmul := mul_le_mul_of_nonneg_left hin hh
    dsimp [point] at hu
    push_cast at hu
    constructor <;> nlinarith [hu.1,hu.2]
  have hm (i : ℕ) (hi : i < n) : 2 ≤ (point h i+point h (i+1))/2 := by
    have hp := hsub i hi (show point h i ∈ Icc (point h i) (point h (i+1)) from ⟨le_rfl,hstep i hi⟩)
    linarith only [hp.1,hstep i hi]
  have he := ClassicalMidpoint.panels_upper hstep
    (fun i hi u hu => ClassicalC.left_deriv (hsub i hi hu).1)
    (fun i hi u hu => ClassicalC.leftD1_deriv (hsub i hi hu).1)
    (fun i hi u hu => (ClassicalC.left_bounds (hsub i hi hu).1 (hsub i hi hu).2).2.2.2)
    (fun i hi => upperValue_bounds (hm i hi))
  simp_rw [hwidth] at he
  rw [sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at he
  have hb : B (3+h*n) = ∫ u in point h 0..point h n, ClassicalC.left u := by
    rw [B_literal (by nlinarith [mul_nonneg hh (Nat.cast_nonneg n)])]
    simp only [point,Nat.cast_zero,mul_zero,add_zero,ClassicalC.left]
    congr 1
    ring
  rw [hb]
  have hpay := mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => hq i (mem_range.mp hi))) hh
  linarith only [he,hpay]

end WuPaper.ClassicalB
#print axioms WuPaper.ClassicalB.prefix_upper
