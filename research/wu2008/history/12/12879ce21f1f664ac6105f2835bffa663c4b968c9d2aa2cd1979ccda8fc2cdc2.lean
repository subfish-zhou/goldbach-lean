import WSrcBuchstabData

namespace WuSource.SrcBuchstab

theorem step_20 :
    deficit (residual (left 20) row20 row00) (1 / 20) ≤
      residual (left 20) row20 row00 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row20, row00]
  norm_num

theorem step_21 :
    deficit (residual (left 21) row21 row01) (1 / 20) ≤
      residual (left 21) row21 row01 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row21, row01]
  norm_num

theorem join_21 : poly row20 (1 / 20) ≤ row21 0 := by
  dsimp [poly, row20, row21]
  norm_num

theorem step_22 :
    deficit (residual (left 22) row22 row02) (1 / 20) ≤
      residual (left 22) row22 row02 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row22, row02]
  norm_num

theorem join_22 : poly row21 (1 / 20) ≤ row22 0 := by
  dsimp [poly, row21, row22]
  norm_num

theorem step_23 :
    deficit (residual (left 23) row23 row03) (1 / 20) ≤
      residual (left 23) row23 row03 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row23, row03]
  norm_num

theorem join_23 : poly row22 (1 / 20) ≤ row23 0 := by
  dsimp [poly, row22, row23]
  norm_num

theorem step_24 :
    deficit (residual (left 24) row24 row04) (1 / 20) ≤
      residual (left 24) row24 row04 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row24, row04]
  norm_num

theorem join_24 : poly row23 (1 / 20) ≤ row24 0 := by
  dsimp [poly, row23, row24]
  norm_num

theorem step_25 :
    deficit (residual (left 25) row25 row05) (1 / 20) ≤
      residual (left 25) row25 row05 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row25, row05]
  norm_num

theorem join_25 : poly row24 (1 / 20) ≤ row25 0 := by
  dsimp [poly, row24, row25]
  norm_num

theorem step_26 :
    deficit (residual (left 26) row26 row06) (1 / 20) ≤
      residual (left 26) row26 row06 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row26, row06]
  norm_num

theorem join_26 : poly row25 (1 / 20) ≤ row26 0 := by
  dsimp [poly, row25, row26]
  norm_num

theorem step_27 :
    deficit (residual (left 27) row27 row07) (1 / 20) ≤
      residual (left 27) row27 row07 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row27, row07]
  norm_num

theorem join_27 : poly row26 (1 / 20) ≤ row27 0 := by
  dsimp [poly, row26, row27]
  norm_num

theorem step_28 :
    deficit (residual (left 28) row28 row08) (1 / 20) ≤
      residual (left 28) row28 row08 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row28, row08]
  norm_num

theorem join_28 : poly row27 (1 / 20) ≤ row28 0 := by
  dsimp [poly, row27, row28]
  norm_num

theorem step_29 :
    deficit (residual (left 29) row29 row09) (1 / 20) ≤
      residual (left 29) row29 row09 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row29, row09]
  norm_num

theorem join_29 : poly row28 (1 / 20) ≤ row29 0 := by
  dsimp [poly, row28, row29]
  norm_num

theorem step_30 :
    deficit (residual (left 30) row30 row10) (1 / 20) ≤
      residual (left 30) row30 row10 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row30, row10]
  norm_num

theorem join_30 : poly row29 (1 / 20) ≤ row30 0 := by
  dsimp [poly, row29, row30]
  norm_num

theorem step_31 :
    deficit (residual (left 31) row31 row11) (1 / 20) ≤
      residual (left 31) row31 row11 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row31, row11]
  norm_num

theorem join_31 : poly row30 (1 / 20) ≤ row31 0 := by
  dsimp [poly, row30, row31]
  norm_num

theorem step_32 :
    deficit (residual (left 32) row32 row12) (1 / 20) ≤
      residual (left 32) row32 row12 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row32, row12]
  norm_num

theorem join_32 : poly row31 (1 / 20) ≤ row32 0 := by
  dsimp [poly, row31, row32]
  norm_num

theorem step_33 :
    deficit (residual (left 33) row33 row13) (1 / 20) ≤
      residual (left 33) row33 row13 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row33, row13]
  norm_num

theorem join_33 : poly row32 (1 / 20) ≤ row33 0 := by
  dsimp [poly, row32, row33]
  norm_num

theorem step_34 :
    deficit (residual (left 34) row34 row14) (1 / 20) ≤
      residual (left 34) row34 row14 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row34, row14]
  norm_num

theorem join_34 : poly row33 (1 / 20) ≤ row34 0 := by
  dsimp [poly, row33, row34]
  norm_num

theorem step_35 :
    deficit (residual (left 35) row35 row15) (1 / 20) ≤
      residual (left 35) row35 row15 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row35, row15]
  norm_num

theorem join_35 : poly row34 (1 / 20) ≤ row35 0 := by
  dsimp [poly, row34, row35]
  norm_num

end WuSource.SrcBuchstab
