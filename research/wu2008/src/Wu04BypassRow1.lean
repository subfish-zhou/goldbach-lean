import Wu04BypassData

namespace Wu04Bypass
open ActualNineFeedback NodeExtension Wu2008DoubleSieve FirstFeedbackIntegrals

theorem matrix_row1 (k : Fin 9) : M 1 k ≤ elementaryMatrix 1 k := by
  fin_cases k <;> norm_num [M, elementaryMatrix, cell, cellLeft, upperNode, upperLeft, coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1, SecondFunctionalParameters.row2, SecondFunctionalParameters.row3, SecondFunctionalParameters.row4, firstS]

end Wu04Bypass
