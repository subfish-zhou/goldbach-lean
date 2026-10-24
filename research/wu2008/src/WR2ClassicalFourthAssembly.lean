import WR2ClassicalFourthRecurrence

noncomputable section
namespace WuPaper.ClassicalFourthRecurrence
open Real Set MeasureTheory ClassicalFourth Wu08TerminalAlignment
open scoped Interval

/-- The shared outer cumulative table pays both recurrence ranges without a new rounding step. -/
theorem fourth_upper_of_table (q U : ℕ → ℝ) (h0 : U 0 = 0)
    (hqi : ∀ i ≤ 8000, kernel initial (node 3 i) ≤ q i)
    (hqt : ∀ i ≤ 2540, kernel terminal (node 5 i) ≤ q (8000+i))
    (hpay : ∀ i < 10540, (1:ℝ)/4000*(q i+q (i+1))/2+
      56*((1:ℝ)/4000)^3/6 ≤ U (i+1)-U i) : fourthMain ≤ 4*U 10540 := by
  have hi := initial_segment_upper (n := 8000) (grid := node 3) (q := q) (U := U) h0
    (fun i _ => node_mono 3 (by omega))
    (fun i hi => by
      have h := node_bounds (3:ℝ) hi
      norm_num at h
      exact h)
    hqi (fun i hi => by rw [node_width]; exact hpay i (by omega))
  have ht := terminal_segment_upper (n := 2540) (grid := node 5)
    (q := fun i => q (8000+i)) (U := fun i => U (8000+i)-U 8000)
    (by simp) (fun i _ => node_mono 5 (by omega))
    (fun i hi => by
      have h := node_bounds (5:ℝ) hi
      norm_num [ClassicalFourth.R] at h ⊢
      exact h)
    hqt (fun i hi => by
      rw [node_width]
      have h := hpay (8000+i) (by omega)
      convert h using 1 <;> first | rfl | (simp only [Nat.add_assoc]; ring))
  have hi0 : node 3 0 = (3:ℝ) := by norm_num [node]
  have hin : node 3 8000 = (5:ℝ) := by norm_num [node]
  have ht0 : node 5 0 = (5:ℝ) := by norm_num [node]
  have htn : node 5 2540 = ClassicalFourth.R-1 := by norm_num [node,ClassicalFourth.R]
  rw [hi0,hin] at hi
  rw [ht0,htn] at ht
  norm_num only [show 8000+2540=10540 by norm_num] at ht
  rw [fourth_split]
  linarith only [hi,ht]

end WuPaper.ClassicalFourthRecurrence
#print axioms WuPaper.ClassicalFourthRecurrence.fourth_upper_of_table
