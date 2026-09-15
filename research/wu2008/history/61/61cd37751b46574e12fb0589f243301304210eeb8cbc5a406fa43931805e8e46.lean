import SrcBuchstabData

namespace WuSource.SrcBuchstab

theorem base_test :
    deficit (baseCoeffs (left 1) row01) (1 / 20) ≤
      baseCoeffs (left 1) row01 0 ∧ 0 ≤ row01 6 := by
  dsimp [deficit, baseCoeffs, left, row01]
  norm_num

theorem cap_test (j : Fin 7) :
    bernstein row48 (1 / 20) j ≤ 561522 / 1000000 := by
  fin_cases j <;> dsimp [bernstein, poly, row48] <;> norm_num

end WuSource.SrcBuchstab
