import WR2ClassicalDTable
import WR2ClassicalFourthTable

noncomputable section
namespace WuPaper.ClassicalFourthRecurrence
open Real Set Wu08OriginalFirstSteps

def node (a : ℝ) (i : ℕ) : ℝ := a+(i:ℝ)/4000

theorem node_width (a : ℝ) (i : ℕ) : node a (i+1)-node a i = (1:ℝ)/4000 := by
  simp only [node,Nat.cast_add,Nat.cast_one]
  ring

theorem node_mono (a : ℝ) {i j : ℕ} (hij : i ≤ j) : node a i ≤ node a j := by
  have h : (i:ℝ) ≤ j := by exact_mod_cast hij
  unfold node
  linarith only [h]

theorem node_bounds (a : ℝ) {i n : ℕ} (hi : i ≤ n) : node a i ∈ Icc a (a+(n:ℝ)/4000) := by
  have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have h1 : (i:ℝ) ≤ n := by exact_mod_cast hi
  unfold node
  constructor <;> linarith only [h0,h1]

/-- A single cumulative B table controls every outer-grid endpoint. -/
theorem B_node_upper (q U : ℕ → ℝ) (h0 : U 0 = 0)
    (hq : ∀ i ≤ 10540, ClassicalB.splitUpper (node 2 i) ≤ q i)
    (hpay : ∀ i < 10540, (1:ℝ)/4000*(q i+q (i+1))/2+
      2*((1:ℝ)/4000)^3/6 ≤ U (i+1)-U i)
    {n : ℕ} (hn : n ≤ 10540) : B (node 3 n) ≤ U n := by
  have hg (i : ℕ) (hi : i ≤ n) : node 2 i ∈ Icc (2:ℝ) 5 := by
    have h := node_bounds (2:ℝ) (hi.trans hn)
    norm_num at h
    exact ⟨h.1,h.2.trans (by norm_num)⟩
  have he := ClassicalB.table_upper (grid := node 2) (q := q) (U := U)
    (by simp [node]) h0 (fun i _ => node_mono 2 (by omega)) hg
    (fun i hi => (ClassicalB.left_le_splitUpper (hg i hi).1).trans (hq i (hi.trans hn)))
    (fun i hi => by rw [node_width]; exact hpay i (by omega))
  have hend : node 2 n+1 = node 3 n := by unfold node; ring
  rwa [hend] at he

/-- The next table consumes B at the same indices, divided by its original parameter. -/
theorem C_node_upper (b U : ℕ → ℝ) (h0 : U 0 = 0)
    (hb : ∀ i ≤ 2540, B (node 3 i) ≤ b i)
    (hpay : ∀ i < 2540, (1:ℝ)/4000*(b i/node 3 i+b (i+1)/node 3 (i+1))/2+
      2*((1:ℝ)/4000)^3/6 ≤ U (i+1)-U i)
    {n : ℕ} (hn : n ≤ 2540) : C (node 4 n) ≤ U n := by
  have hg (i : ℕ) (hi : i ≤ n) : node 3 i ∈ Icc (3:ℝ) 6 := by
    have h := node_bounds (3:ℝ) (hi.trans hn)
    norm_num at h
    exact ⟨h.1,h.2.trans (by norm_num)⟩
  have he := ClassicalCTable.table_upper (grid := node 3) (q := fun i => b i/node 3 i) (U := U)
    (by simp [node]) h0 (fun i _ => node_mono 3 (by omega)) hg
    (fun i hi => div_le_div_of_nonneg_right (hb i (hi.trans hn)) (by linarith [(hg i hi).1]))
    (fun i hi => by rw [node_width]; exact hpay i (by omega))
  have hend : node 3 n+1 = node 4 n := by unfold node; ring
  rwa [hend] at he

theorem D_node_upper (c U : ℕ → ℝ) (h0 : U 0 = 0)
    (hc : ∀ i ≤ 2540, C (node 4 i) ≤ c i)
    (hpay : ∀ i < 2540, (1:ℝ)/4000*(c i/node 4 i+c (i+1)/node 4 (i+1))/2+
      1*((1:ℝ)/4000)^3/6 ≤ U (i+1)-U i)
    {n : ℕ} (hn : n ≤ 2540) : D (node 5 n) ≤ U n := by
  have hg (i : ℕ) (hi : i ≤ n) : node 4 i ∈ Icc (4:ℝ) 6 := by
    have h := node_bounds (4:ℝ) (hi.trans hn)
    norm_num at h
    exact ⟨h.1,h.2.trans (by norm_num)⟩
  have he := ClassicalDTable.table_upper (grid := node 4) (q := fun i => c i/node 4 i) (U := U)
    (by simp [node]) h0 (fun i _ => node_mono 4 (by omega)) hg
    (fun i hi => div_le_div_of_nonneg_right (hc i (hi.trans hn)) (by linarith [(hg i hi).1]))
    (fun i hi => by rw [node_width]; exact hpay i (by omega))
  have hend : node 4 n+1 = node 5 n := by unfold node; ring
  rwa [hend] at he

end WuPaper.ClassicalFourthRecurrence
#print axioms WuPaper.ClassicalFourthRecurrence.B_node_upper
#print axioms WuPaper.ClassicalFourthRecurrence.C_node_upper
#print axioms WuPaper.ClassicalFourthRecurrence.D_node_upper
