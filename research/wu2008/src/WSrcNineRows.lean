import WSrcNineRow0

noncomputable section
namespace WuSource.SrcNine
open NodeExtension ActualNineFeedback WuTarget

theorem row1 : z 1 ≤ W09.seed 1 + matrixApply W17Joint.jointMatrix z 1 := by
  src_nine_scalar

theorem row2 : z 2 ≤ W09.seed 2 + matrixApply W17Joint.jointMatrix z 2 := by
  src_nine_scalar

theorem row3 : z 3 ≤ W09.seed 3 + matrixApply W17Joint.jointMatrix z 3 := by
  src_nine_scalar

theorem row4 : z 4 ≤ W09.seed 4 + matrixApply W17Joint.jointMatrix z 4 := by
  src_nine_scalar

theorem row5 : z 5 ≤ W09.seed 5 + matrixApply W17Joint.jointMatrix z 5 := by
  src_nine_scalar

theorem row6 : z 6 ≤ W09.seed 6 + matrixApply W17Joint.jointMatrix z 6 := by
  src_nine_scalar

theorem row7 : z 7 ≤ W09.seed 7 + matrixApply W17Joint.jointMatrix z 7 := by
  src_nine_scalar

theorem row8 : z 8 ≤ W09.seed 8 + matrixApply W17Joint.jointMatrix z 8 := by
  src_nine_scalar

theorem all_rows (i : Fin 9) :
    z i ≤ W09.seed i + matrixApply W17Joint.jointMatrix z i := by
  fin_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8

end WuSource.SrcNine
