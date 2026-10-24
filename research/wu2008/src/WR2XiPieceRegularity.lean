import WR2XiPieces

/-! Continuity on the literal original four-row supports pays piece integrability. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open WuPaper.RMapMMatrix SecondFunctionalParameters
open scoped Interval

set_option maxHeartbeats 1600000 in
theorem original_piece_continuous (r : Fin 4) (j : Fin 9) :
    ContinuousOn (fun t => xi2PieceKernel (gamma5OriginalRow r) t j)
      (Icc (xi2PieceInterval (gamma5OriginalRow r) j).1
        (xi2PieceInterval (gamma5OriginalRow r) j).2) := by
  intro t ht
  rcases ht with ⟨htlo, hthi⟩
  apply ContinuousAt.continuousWithinAt
  fin_cases r <;> fin_cases j <;>
    norm_num [xi2PieceKernel, xi2PieceInterval, xi2ParameterProduct, gamma5OriginalRow,
      row1, row2, row3, row4, alpha1, alpha2, alpha3, alpha4, alpha5, alpha6,
      alpha7, alpha8, alpha9] at htlo hthi ⊢ <;>
    have htpos : 0 < t := by linarith
  all_goals fun_prop (disch := first | positivity |
    (apply div_ne_zero <;> first | positivity | nlinarith) | nlinarith)

theorem original_piece_integrable (r : Fin 4) (j : Fin 9) :
    Integrable (xi2Piece (gamma5OriginalRow r) j) :=
  (original_piece_continuous r j).integrableOn_Icc.integrable_indicator measurableSet_Icc

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_piece_integrable
