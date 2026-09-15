import W08EntriesRest

noncomputable section
namespace WuTarget.W08
open Wu2008DoubleSieve ActualNineFeedback NodeExtension FirstFeedbackIntegrals
open scoped BigOperators

theorem paidMatrix_row0 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 0 k < paidMatrix 0 k := by
  fin_cases k <;> first
    | exact entry00 | exact entry01 | exact entry02 | exact entry03 | exact entry04
    | exact entry05 | exact entry06 | exact entry07 | exact entry08

theorem paidMatrix_row1 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 1 k < paidMatrix 1 k := by
  fin_cases k <;> first
    | exact entry10 | exact entry11 | exact entry12 | exact entry13 | exact entry14
    | exact entry15 | exact entry16 | exact entry17 | exact entry18

theorem paidMatrix_row2 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 2 k < paidMatrix 2 k := by
  fin_cases k <;> first
    | exact entry20 | exact entry21 | exact entry22 | exact entry23 | exact entry24
    | exact entry25 | exact entry26 | exact entry27 | exact entry28

theorem paidMatrix_row3 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 3 k < paidMatrix 3 k := by
  fin_cases k <;> first
    | exact entry30 | exact entry31 | exact entry32 | exact entry33 | exact entry34
    | exact entry35 | exact entry36 | exact entry37 | exact entry38

theorem paidMatrix_row4 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 4 k < paidMatrix 4 k := by
  fin_cases k <;> first
    | exact entry40 | exact entry41 | exact entry42 | exact entry43 | exact entry44
    | exact entry45 | exact entry46 | exact entry47 | exact entry48

theorem paidMatrix_row5 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 5 k < paidMatrix 5 k := by
  fin_cases k <;> first
    | exact entry50 | exact entry51 | exact entry52 | exact entry53 | exact entry54
    | exact entry55 | exact entry56 | exact entry57 | exact entry58

theorem paidMatrix_row6 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 6 k < paidMatrix 6 k := by
  fin_cases k <;> first
    | exact entry60 | exact entry61 | exact entry62 | exact entry63 | exact entry64
    | exact entry65 | exact entry66 | exact entry67 | exact entry68

theorem paidMatrix_row7 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 7 k < paidMatrix 7 k := by
  fin_cases k <;> first
    | exact entry70 | exact entry71 | exact entry72 | exact entry73 | exact entry74
    | exact entry75 | exact entry76 | exact entry77 | exact entry78

theorem paidMatrix_row8 (k : Fin 9) :
    Wu04Bypass.elementaryMatrix 8 k < paidMatrix 8 k := by
  fin_cases k <;> first
    | exact entry80 | exact entry81 | exact entry82 | exact entry83 | exact entry84
    | exact entry85 | exact entry86 | exact entry87 | exact entry88

theorem elementaryMatrix_lt_paidMatrix (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k < paidMatrix i k := by
  fin_cases i
  · exact paidMatrix_row0 k
  · exact paidMatrix_row1 k
  · exact paidMatrix_row2 k
  · exact paidMatrix_row3 k
  · exact paidMatrix_row4 k
  · exact paidMatrix_row5 k
  · exact paidMatrix_row6 k
  · exact paidMatrix_row7 k
  · exact paidMatrix_row8 k

theorem elementaryMatrix_le_paidMatrix (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k ≤ paidMatrix i k :=
  (elementaryMatrix_lt_paidMatrix i k).le

theorem elementaryCell_nonneg {S a b : ℝ} (hS : 3 ≤ S)
    (ha : S - 2 ≤ a) (hab : a ≤ b) : 0 ≤ Wu04Bypass.cell S a b := by
  have hb : 0 < b := by linarith
  unfold Wu04Bypass.cell
  apply div_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  · positivity

theorem elementaryNodeCell_nonneg {S : ℝ} (hS : 3 ≤ S)
    (hcell : S - 2 ≤ upperNode 0) (k : Fin 9) :
    0 ≤ Wu04Bypass.cell S (cellLeft (S - 2) k) (upperNode k) := by
  have hb := cell_bounds (by linarith : 1 ≤ S - 2) hcell k
  exact elementaryCell_nonneg hS hb.1 hb.2.1

theorem elementaryMatrix_nonneg (i k : Fin 9) :
    0 ≤ Wu04Bypass.elementaryMatrix i k := by
  unfold Wu04Bypass.elementaryMatrix
  split_ifs with h
  · exact div_nonneg
      (elementaryNodeCell_nonneg (coupledRow_geometry ⟨i.val, h⟩).2.1
        (Wu04Bypass.coupled_kappa_cell ⟨i.val, h⟩) k) (by norm_num)
  · exact elementaryNodeCell_nonneg (first_geometry ⟨i.val - 4, by omega⟩).2.2.1
      (Wu04Bypass.first_cell ⟨i.val - 4, by omega⟩) k

theorem paidMatrix_pos (i k : Fin 9) : 0 < paidMatrix i k :=
  (elementaryMatrix_nonneg i k).trans_lt (elementaryMatrix_lt_paidMatrix i k)

theorem paidMatrix_nonneg (i k : Fin 9) : 0 ≤ paidMatrix i k :=
  (paidMatrix_pos i k).le

/-- This increment is an approximation improvement, not another feedback term. -/
def eGainMatrix (i k : Fin 9) : ℝ :=
  paidMatrix i k - Wu04Bypass.elementaryMatrix i k

theorem eGainMatrix_pos (i k : Fin 9) : 0 < eGainMatrix i k :=
  sub_pos.mpr (elementaryMatrix_lt_paidMatrix i k)

theorem elementary_add_gain (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k + eGainMatrix i k = paidMatrix i k := by
  unfold eGainMatrix
  ring

theorem elementary_add_gain_le (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k + eGainMatrix i k ≤ feedbackMatrix i k := by
  rw [elementary_add_gain]
  exact paidMatrix_le i k

theorem apply_comparison {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    (∑ k : Fin 9, Wu04Bypass.elementaryMatrix i k * z k) ≤
      (∑ k : Fin 9, paidMatrix i k * z k) ∧
    (∑ k : Fin 9, paidMatrix i k * z k) ≤ feedback z i := by
  exact ⟨Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (elementaryMatrix_le_paidMatrix i k) (hz k)),
    paidMatrix_apply_le_feedback hz i⟩

theorem apply_strict {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    (hpos : ∃ k, 0 < z k) (i : Fin 9) :
    (∑ k : Fin 9, Wu04Bypass.elementaryMatrix i k * z k) <
      (∑ k : Fin 9, paidMatrix i k * z k) := by
  apply Finset.sum_lt_sum
  · intro k _
    exact mul_le_mul_of_nonneg_right (elementaryMatrix_le_paidMatrix i k) (hz k)
  · obtain ⟨k, hk⟩ := hpos
    exact ⟨k, Finset.mem_univ k,
      mul_lt_mul_of_pos_right (elementaryMatrix_lt_paidMatrix i k) hk⟩

theorem apply_gain_eq (z : Fin 9 → ℝ) (i : Fin 9) :
    (∑ k : Fin 9, Wu04Bypass.elementaryMatrix i k * z k) +
      (∑ k : Fin 9, eGainMatrix i k * z k) =
      (∑ k : Fin 9, paidMatrix i k * z k) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← add_mul, elementary_add_gain]

end WuTarget.W08
