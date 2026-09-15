import SrcFifthGainWeight

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def node (i : ℕ) : ℝ := 2+(i : ℝ)/10
def cellLower (j : ℕ) : ℝ := max s0 (node (14+j))
def cellUpper (j : ℕ) : ℝ := min FifthClassicalShape.q (node (15+j))
def cell (j : ℕ) : Set ℝ := Ioc (cellLower j) (cellUpper j)
def edge (k : ℕ) : ℝ :=
  if k = 0 then s0 else if k = 13 then FifthClassicalShape.q else node (14+k)
def cellWeight (j : ℕ) : ℝ := ∫ s in cellLower j..cellUpper j, weight s

theorem cell_geometry {j : ℕ} (hj : j < 13) :
    s0 ≤ cellLower j ∧ cellLower j ≤ cellUpper j ∧
      cellUpper j ≤ FifthClassicalShape.q ∧ cellUpper j ≤ node (15+j) ∧
      node (15+j) ∈ Icc (2 : ℝ) 10 := by
  interval_cases j <;>
    norm_num [cellLower, cellUpper, node, s0, FifthClassicalShape.q, a, b,
      truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem cell_edges {j : ℕ} (hj : j < 13) :
    cellLower j = edge j ∧ cellUpper j = edge (j+1) := by
  interval_cases j <;>
    norm_num [cellLower, cellUpper, edge, node, s0, FifthClassicalShape.q, a, b,
      truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem adjacent_cover (f : ℕ → ℝ) (n : ℕ) {s : ℝ}
    (hs : f 0 < s) (ht : s ≤ f n) :
    ∃ j < n, f j < s ∧ s ≤ f (j+1) := by
  induction n with
  | zero => exact False.elim (not_lt_of_ge ht hs)
  | succ n ih =>
    by_cases hn : s ≤ f n
    · obtain ⟨j, hj, hh⟩ := ih hn
      exact ⟨j, Nat.lt_succ_of_lt hj, hh⟩
    · exact ⟨n, Nat.lt_succ_self n, lt_of_not_ge hn, ht⟩

theorem thirteen_cell_cover :
    Ioc s0 FifthClassicalShape.q = ⋃ j ∈ Finset.range 13, cell j := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, hj, hh⟩ := adjacent_cover edge 13
      (by simpa [edge] using hs.1) (by simpa [edge] using hs.2)
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,
      by simpa only [cell, (cell_edges hj).1, (cell_edges hj).2, mem_Ioc] using hh⟩⟩
  · intro hs
    obtain ⟨j, hs⟩ := mem_iUnion.mp hs
    obtain ⟨hj, hs⟩ := mem_iUnion.mp hs
    have hg := cell_geometry (Finset.mem_range.mp hj)
    exact ⟨hg.1.trans_lt hs.1, hs.2.trans hg.2.2.1⟩

theorem cells_ordered {i j : ℕ} (hij : i < j) :
    cellUpper i ≤ cellLower j := by
  apply (min_le_right _ _).trans
  apply le_trans _ (le_max_right _ _)
  unfold node
  have hn : 15+i ≤ 14+j := by omega
  have hnr : ((15+i : ℕ) : ℝ) ≤ ((14+j : ℕ) : ℝ) := by exact_mod_cast hn
  linarith only [hnr]

theorem cell_unique {i j : ℕ} {s : ℝ} (hi : s ∈ cell i) (hj : s ∈ cell j) :
    i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (not_lt_of_ge (hi.2.trans (cells_ordered hij)) hj.1)
  · exact hij
  · exact False.elim (not_lt_of_ge (hj.2.trans (cells_ordered hij)) hi.1)

theorem first_cell :
    cellLower 0 = s0 ∧ cellUpper 0 = node 15 := by
  norm_num [cellLower, cellUpper, node, s0, FifthClassicalShape.q, a, b,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem last_cell :
    cellLower 12 = node 26 ∧ cellUpper 12 = FifthClassicalShape.q ∧
      FifthClassicalShape.q < node 27 := by
  norm_num [cellLower, cellUpper, node, s0, FifthClassicalShape.q, a, b,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem cross_cell :
    cellLower 6 = node 20 ∧ cellUpper 6 = node 21 ∧
      node 20 < geometricSplit ∧ geometricSplit < node 21 := by
  norm_num [cellLower, cellUpper, node, s0, FifthClassicalShape.q, geometricSplit, a, b,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem cell_weight_nonneg {j : ℕ} (hj : j < 13) : 0 ≤ cellWeight j := by
  have hg := cell_geometry hj
  exact weight_integral_nonneg hg.1 hg.2.1 hg.2.2.1

theorem cell_weight_integrable {j : ℕ} (hj : j < 13) :
    IntervalIntegrable weight volume (cellLower j) (cellUpper j) := by
  have hg := cell_geometry hj
  exact weight_integrable_sub hg.1 hg.2.1 hg.2.2.1

theorem cell_weight_first :
    cellWeight 0 = ∫ s in s0..node 15, lowerWeight s := by
  rw [cellWeight, first_cell.1, first_cell.2]
  apply lower_integral_literal le_rfl
  · norm_num [node, s0, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  · norm_num [node, geometricSplit, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem cell_weight_lower {j : ℕ} (hj : 1 ≤ j) (hj5 : j ≤ 5) :
    cellWeight j = ∫ s in node (14+j)..node (15+j), lowerWeight s := by
  have hb : cellLower j = node (14+j) ∧ cellUpper j = node (15+j) ∧
      node (15+j) ≤ geometricSplit := by
    interval_cases j <;>
      norm_num [cellLower, cellUpper, node, s0, FifthClassicalShape.q, geometricSplit,
        a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  have hg := cell_geometry (by omega : j < 13)
  rw [cellWeight, lower_integral_literal hg.1 hg.2.1 (hb.2.1.le.trans hb.2.2), hb.1, hb.2.1]

theorem cell_weight_cross :
    cellWeight 6 =
      (∫ s in node 20..geometricSplit, lowerWeight s)+
      ∫ s in geometricSplit..node 21, upperWeight s := by
  have hg := cell_geometry (by norm_num : 6 < 13)
  have hc := cross_cell
  have hi1 := weight_integrable_sub (hc.1 ▸ hg.1) hc.2.2.1.le
    (hc.2.2.2.le.trans (hc.2.1 ▸ hg.2.2.1))
  have hi2 := weight_integrable_sub
    ((hc.1 ▸ hg.1).trans hc.2.2.1.le) hc.2.2.2.le (hc.2.1 ▸ hg.2.2.1)
  rw [cellWeight, hc.1, hc.2.1,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    lower_integral_literal (hc.1 ▸ hg.1) hc.2.2.1.le le_rfl,
    upper_integral_literal le_rfl hc.2.2.2.le (hc.2.1 ▸ hg.2.2.1)]

theorem cell_weight_upper {j : ℕ} (hj : 7 ≤ j) (hj11 : j ≤ 11) :
    cellWeight j = ∫ s in node (14+j)..node (15+j), upperWeight s := by
  have hb : cellLower j = node (14+j) ∧ cellUpper j = node (15+j) ∧
      geometricSplit ≤ node (14+j) := by
    interval_cases j <;>
      norm_num [cellLower, cellUpper, node, s0, FifthClassicalShape.q, geometricSplit,
        a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  have hg := cell_geometry (by omega : j < 13)
  rw [cellWeight, upper_integral_literal (hb.2.2.trans hb.1.symm.le) hg.2.1 hg.2.2.1,
    hb.1, hb.2.1]

theorem cell_weight_last :
    cellWeight 12 = ∫ s in node 26..FifthClassicalShape.q, upperWeight s := by
  rw [cellWeight, last_cell.1, last_cell.2.1]
  apply upper_integral_literal _ _ le_rfl
  · norm_num [node, geometricSplit, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  · norm_num [node, FifthClassicalShape.q, a, truncatedSixthLowerAlpha]

end
end WuSource.SrcFifthGain
