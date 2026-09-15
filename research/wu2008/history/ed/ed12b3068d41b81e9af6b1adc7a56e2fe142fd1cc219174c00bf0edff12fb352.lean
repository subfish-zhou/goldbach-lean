import WSrcBuchstabData

namespace WuSource.SrcBuchstab

theorem step_36 :
    deficit (residual (left 36) row36 row16) (1 / 20) ≤
      residual (left 36) row36 row16 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row36, row16]
  norm_num

theorem join_36 : poly row35 (1 / 20) ≤ row36 0 := by
  dsimp [poly, row35, row36]
  norm_num

theorem step_37 :
    deficit (residual (left 37) row37 row17) (1 / 20) ≤
      residual (left 37) row37 row17 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row37, row17]
  norm_num

theorem join_37 : poly row36 (1 / 20) ≤ row37 0 := by
  dsimp [poly, row36, row37]
  norm_num

theorem step_38 :
    deficit (residual (left 38) row38 row18) (1 / 20) ≤
      residual (left 38) row38 row18 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row38, row18]
  norm_num

theorem join_38 : poly row37 (1 / 20) ≤ row38 0 := by
  dsimp [poly, row37, row38]
  norm_num

theorem step_39 :
    deficit (residual (left 39) row39 row19) (1 / 20) ≤
      residual (left 39) row39 row19 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row39, row19]
  norm_num

theorem join_39 : poly row38 (1 / 20) ≤ row39 0 := by
  dsimp [poly, row38, row39]
  norm_num

theorem step_40 :
    deficit (residual (left 40) row40 row20) (1 / 20) ≤
      residual (left 40) row40 row20 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row40, row20]
  norm_num

theorem join_40 : poly row39 (1 / 20) ≤ row40 0 := by
  dsimp [poly, row39, row40]
  norm_num

theorem step_41 :
    deficit (residual (left 41) row41 row21) (1 / 20) ≤
      residual (left 41) row41 row21 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row41, row21]
  norm_num

theorem join_41 : poly row40 (1 / 20) ≤ row41 0 := by
  dsimp [poly, row40, row41]
  norm_num

theorem step_42 :
    deficit (residual (left 42) row42 row22) (1 / 20) ≤
      residual (left 42) row42 row22 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row42, row22]
  norm_num

theorem join_42 : poly row41 (1 / 20) ≤ row42 0 := by
  dsimp [poly, row41, row42]
  norm_num

theorem step_43 :
    deficit (residual (left 43) row43 row23) (1 / 20) ≤
      residual (left 43) row43 row23 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row43, row23]
  norm_num

theorem join_43 : poly row42 (1 / 20) ≤ row43 0 := by
  dsimp [poly, row42, row43]
  norm_num

theorem step_44 :
    deficit (residual (left 44) row44 row24) (1 / 20) ≤
      residual (left 44) row44 row24 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row44, row24]
  norm_num

theorem join_44 : poly row43 (1 / 20) ≤ row44 0 := by
  dsimp [poly, row43, row44]
  norm_num

theorem step_45 :
    deficit (residual (left 45) row45 row25) (1 / 20) ≤
      residual (left 45) row45 row25 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row45, row25]
  norm_num

theorem join_45 : poly row44 (1 / 20) ≤ row45 0 := by
  dsimp [poly, row44, row45]
  norm_num

theorem step_46 :
    deficit (residual (left 46) row46 row26) (1 / 20) ≤
      residual (left 46) row46 row26 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row46, row26]
  norm_num

theorem join_46 : poly row45 (1 / 20) ≤ row46 0 := by
  dsimp [poly, row45, row46]
  norm_num

theorem step_47 :
    deficit (residual (left 47) row47 row27) (1 / 20) ≤
      residual (left 47) row47 row27 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row47, row27]
  norm_num

theorem join_47 : poly row46 (1 / 20) ≤ row47 0 := by
  dsimp [poly, row46, row47]
  norm_num

theorem step_48 :
    deficit (residual (left 48) row48 row28) (1 / 20) ≤
      residual (left 48) row48 row28 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row48, row28]
  norm_num

theorem join_48 : poly row47 (1 / 20) ≤ row48 0 := by
  dsimp [poly, row47, row48]
  norm_num

theorem cap_48 (j : Fin 7) :
    bernstein row48 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row48] <;> norm_num

theorem step_49 :
    deficit (residual (left 49) row49 row29) (1 / 20) ≤
      residual (left 49) row49 row29 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row49, row29]
  norm_num

theorem join_49 : poly row48 (1 / 20) ≤ row49 0 := by
  dsimp [poly, row48, row49]
  norm_num

theorem cap_49 (j : Fin 7) :
    bernstein row49 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row49] <;> norm_num

theorem step_50 :
    deficit (residual (left 50) row50 row30) (1 / 20) ≤
      residual (left 50) row50 row30 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row50, row30]
  norm_num

theorem join_50 : poly row49 (1 / 20) ≤ row50 0 := by
  dsimp [poly, row49, row50]
  norm_num

theorem cap_50 (j : Fin 7) :
    bernstein row50 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row50] <;> norm_num

theorem step_51 :
    deficit (residual (left 51) row51 row31) (1 / 20) ≤
      residual (left 51) row51 row31 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row51, row31]
  norm_num

theorem join_51 : poly row50 (1 / 20) ≤ row51 0 := by
  dsimp [poly, row50, row51]
  norm_num

theorem cap_51 (j : Fin 7) :
    bernstein row51 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row51] <;> norm_num

end WuSource.SrcBuchstab
