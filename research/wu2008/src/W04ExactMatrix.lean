import W04CoupledMatrix

noncomputable section
namespace WuTarget.W04
open NodeExtension ActualNineFeedback Wu2008DoubleSieve

def extraTable : Fin 4 → Fin 9 → ℝ :=
  ![![0, 0, 0, 0, 1/6500, 22/24975, 3/1900, 62/28275, 41/15000],
    ![0, 0, 0, 0, 1/2340, 2/1665, 1/532, 14/5655, 3/1000],
    ![0, 0, 0, 8/109375, 1/1300, 38/24975, 29/13300, 2/725, 49/15000],
    ![1/2750, 26/18975, 23/10200, 66/21875, 43/11700, 106/24975,
      9/1900, 146/28275, 83/15000]]

theorem extra_row0 (k : Fin 9) : coupledExtra 0 k = extraTable 0 k := by
  fin_cases k <;> norm_num [coupledExtra, clippedCell, Wu04Bypass.cell,
    coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
    upperLeft, upperNode, extraTable]

theorem extra_row1 (k : Fin 9) : coupledExtra 1 k = extraTable 1 k := by
  fin_cases k <;> norm_num [coupledExtra, clippedCell, Wu04Bypass.cell,
    coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row2,
    upperLeft, upperNode, extraTable]

theorem extra_row2 (k : Fin 9) : coupledExtra 2 k = extraTable 2 k := by
  change coupledExtra ⟨2, by decide⟩ k = extraTable ⟨2, by decide⟩ k
  fin_cases k <;> norm_num [coupledExtra, clippedCell, Wu04Bypass.cell,
    coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row3,
    upperLeft, upperNode, extraTable]

theorem extra_row3 (k : Fin 9) : coupledExtra 3 k = extraTable 3 k := by
  change coupledExtra ⟨3, by decide⟩ k = extraTable ⟨3, by decide⟩ k
  fin_cases k <;> norm_num [coupledExtra, clippedCell, Wu04Bypass.cell,
    coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row4,
    upperLeft, upperNode, extraTable]

theorem coupledExtra_eq_table (i : Fin 4) (k : Fin 9) :
    coupledExtra i k = extraTable i k := by
  fin_cases i
  · exact extra_row0 k
  · exact extra_row1 k
  · exact extra_row2 k
  · exact extra_row3 k

theorem extraMatrix_eq_table (i k : Fin 9) :
    extraMatrix i k = if h : i.val < 4 then extraTable ⟨i.val, h⟩ k else 0 := by
  unfold extraMatrix
  split_ifs
  · exact coupledExtra_eq_table _ k
  · rfl

theorem extraTable_le_kernel (i : Fin 4) (k : Fin 9) :
    extraTable i k ≤ 4 * eKernel (coupledRow i).S k / 5 := by
  rw [← coupledExtra_eq_table]
  exact coupledExtra_le_kernel i k

theorem explicit_augmentedMatrix_le (i k : Fin 9) :
    Wu04Bypass.M i k +
      (if h : i.val < 4 then extraTable ⟨i.val, h⟩ k else 0) ≤ feedbackMatrix i k := by
  rw [← extraMatrix_eq_table]
  exact augmentedMatrix_le_feedbackMatrix i k

theorem coupledExtra_terminal_pos (i : Fin 4) : 0 < coupledExtra i 8 := by
  rw [coupledExtra_eq_table]
  change 0 < extraTable i ⟨8, by decide⟩
  fin_cases i <;> norm_num [extraTable]

theorem coupled_rows_strictly_improve (i : Fin 4) :
    Wu04Bypass.M ⟨i.val, by omega⟩ 8 < augmentedMatrix ⟨i.val, by omega⟩ 8 := by
  have hi : i.val < 4 := i.isLt
  have h := coupledExtra_terminal_pos i
  simpa only [augmentedMatrix, extraMatrix, dif_pos hi, lt_add_iff_pos_right] using h

end WuTarget.W04
