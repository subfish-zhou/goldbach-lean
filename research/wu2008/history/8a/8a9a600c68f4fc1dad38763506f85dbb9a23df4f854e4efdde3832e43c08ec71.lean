import SrcBuchstabData

namespace WuSource.SrcBuchstab

theorem step_52 :
    deficit (residual (left 52) row52 row32) (1 / 20) ≤
      residual (left 52) row52 row32 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row52, row32]
  norm_num

theorem join_52 : poly row51 (1 / 20) ≤ row52 0 := by
  dsimp [poly, row51, row52]
  norm_num

theorem cap_52 (j : Fin 7) :
    bernstein row52 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row52] <;> norm_num

theorem step_53 :
    deficit (residual (left 53) row53 row33) (1 / 20) ≤
      residual (left 53) row53 row33 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row53, row33]
  norm_num

theorem join_53 : poly row52 (1 / 20) ≤ row53 0 := by
  dsimp [poly, row52, row53]
  norm_num

theorem cap_53 (j : Fin 7) :
    bernstein row53 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row53] <;> norm_num

theorem step_54 :
    deficit (residual (left 54) row54 row34) (1 / 20) ≤
      residual (left 54) row54 row34 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row54, row34]
  norm_num

theorem join_54 : poly row53 (1 / 20) ≤ row54 0 := by
  dsimp [poly, row53, row54]
  norm_num

theorem cap_54 (j : Fin 7) :
    bernstein row54 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row54] <;> norm_num

theorem step_55 :
    deficit (residual (left 55) row55 row35) (1 / 20) ≤
      residual (left 55) row55 row35 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row55, row35]
  norm_num

theorem join_55 : poly row54 (1 / 20) ≤ row55 0 := by
  dsimp [poly, row54, row55]
  norm_num

theorem cap_55 (j : Fin 7) :
    bernstein row55 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row55] <;> norm_num

theorem step_56 :
    deficit (residual (left 56) row56 row36) (1 / 20) ≤
      residual (left 56) row56 row36 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row56, row36]
  norm_num

theorem join_56 : poly row55 (1 / 20) ≤ row56 0 := by
  dsimp [poly, row55, row56]
  norm_num

theorem cap_56 (j : Fin 7) :
    bernstein row56 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row56] <;> norm_num

theorem step_57 :
    deficit (residual (left 57) row57 row37) (1 / 20) ≤
      residual (left 57) row57 row37 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row57, row37]
  norm_num

theorem join_57 : poly row56 (1 / 20) ≤ row57 0 := by
  dsimp [poly, row56, row57]
  norm_num

theorem cap_57 (j : Fin 7) :
    bernstein row57 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row57] <;> norm_num

theorem step_58 :
    deficit (residual (left 58) row58 row38) (1 / 20) ≤
      residual (left 58) row58 row38 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row58, row38]
  norm_num

theorem join_58 : poly row57 (1 / 20) ≤ row58 0 := by
  dsimp [poly, row57, row58]
  norm_num

theorem cap_58 (j : Fin 7) :
    bernstein row58 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row58] <;> norm_num

theorem step_59 :
    deficit (residual (left 59) row59 row39) (1 / 20) ≤
      residual (left 59) row59 row39 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row59, row39]
  norm_num

theorem join_59 : poly row58 (1 / 20) ≤ row59 0 := by
  dsimp [poly, row58, row59]
  norm_num

theorem cap_59 (j : Fin 7) :
    bernstein row59 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row59] <;> norm_num

theorem step_60 :
    deficit (residual (left 60) row60 row40) (1 / 20) ≤
      residual (left 60) row60 row40 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row60, row40]
  norm_num

theorem join_60 : poly row59 (1 / 20) ≤ row60 0 := by
  dsimp [poly, row59, row60]
  norm_num

theorem cap_60 (j : Fin 7) :
    bernstein row60 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row60] <;> norm_num

theorem step_61 :
    deficit (residual (left 61) row61 row41) (1 / 20) ≤
      residual (left 61) row61 row41 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row61, row41]
  norm_num

theorem join_61 : poly row60 (1 / 20) ≤ row61 0 := by
  dsimp [poly, row60, row61]
  norm_num

theorem cap_61 (j : Fin 7) :
    bernstein row61 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row61] <;> norm_num

theorem step_62 :
    deficit (residual (left 62) row62 row42) (1 / 20) ≤
      residual (left 62) row62 row42 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row62, row42]
  norm_num

theorem join_62 : poly row61 (1 / 20) ≤ row62 0 := by
  dsimp [poly, row61, row62]
  norm_num

theorem cap_62 (j : Fin 7) :
    bernstein row62 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row62] <;> norm_num

theorem step_63 :
    deficit (residual (left 63) row63 row43) (1 / 20) ≤
      residual (left 63) row63 row43 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row63, row43]
  norm_num

theorem join_63 : poly row62 (1 / 20) ≤ row63 0 := by
  dsimp [poly, row62, row63]
  norm_num

theorem cap_63 (j : Fin 7) :
    bernstein row63 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row63] <;> norm_num

theorem step_64 :
    deficit (residual (left 64) row64 row44) (1 / 20) ≤
      residual (left 64) row64 row44 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row64, row44]
  norm_num

theorem join_64 : poly row63 (1 / 20) ≤ row64 0 := by
  dsimp [poly, row63, row64]
  norm_num

theorem cap_64 (j : Fin 7) :
    bernstein row64 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row64] <;> norm_num

theorem step_65 :
    deficit (residual (left 65) row65 row45) (1 / 20) ≤
      residual (left 65) row65 row45 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row65, row45]
  norm_num

theorem join_65 : poly row64 (1 / 20) ≤ row65 0 := by
  dsimp [poly, row64, row65]
  norm_num

theorem cap_65 (j : Fin 7) :
    bernstein row65 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row65] <;> norm_num

theorem step_66 :
    deficit (residual (left 66) row66 row46) (1 / 20) ≤
      residual (left 66) row66 row46 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row66, row46]
  norm_num

theorem join_66 : poly row65 (1 / 20) ≤ row66 0 := by
  dsimp [poly, row65, row66]
  norm_num

theorem cap_66 (j : Fin 7) :
    bernstein row66 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row66] <;> norm_num

theorem step_67 :
    deficit (residual (left 67) row67 row47) (1 / 20) ≤
      residual (left 67) row67 row47 0 := by
  dsimp [deficit, residual, weightedCoeffs, left, row67, row47]
  norm_num

theorem join_67 : poly row66 (1 / 20) ≤ row67 0 := by
  dsimp [poly, row66, row67]
  norm_num

theorem cap_67 (j : Fin 7) :
    bernstein row67 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row67] <;> norm_num

end WuSource.SrcBuchstab
