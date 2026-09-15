import Wu04BypassData

namespace Wu04Bypass
open ActualNineFeedback NodeExtension Wu2008DoubleSieve FirstFeedbackIntegrals

theorem matrix_row6 (k : Fin 9) : M ⟨6, by decide⟩ k ≤ elementaryMatrix ⟨6, by decide⟩ k := by
  fin_cases k <;> norm_num [M, elementaryMatrix, cell, cellLeft, upperNode, upperLeft, coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1, SecondFunctionalParameters.row2, SecondFunctionalParameters.row3, SecondFunctionalParameters.row4, firstS]

end Wu04Bypass
