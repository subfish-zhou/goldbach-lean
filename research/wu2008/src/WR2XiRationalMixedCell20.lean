import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import WR2XiRoundedPiece20
import WR2XiRoundedPiece21
import WR2XiRoundedPiece22
import WR2XiRoundedPiece23
import WR2XiRoundedPiece24
import WR2XiRoundedPiece25
import WR2XiRoundedPiece26
import WR2XiRoundedPiece27
import WR2XiRoundedPiece28
namespace Xi2RationalMixed
open Xi2RationalTop
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_2_0 : target 2 0 + (if (0 : Fin 9) = 0 then debit 2 else 0) ≤ entry 2 0 := by
  apply le_trans (b := roundedEntry 2 0) _ (roundedEntry_le 2 0)
  have hpieces : roundedPiece 2 0 = (![0/1000000000000, 5100451865/1000000000000, 17299180216/1000000000000, 17299180216/1000000000000, 35917462400/1000000000000, 8822331092/1000000000000, 3927028917/1000000000000, 6320308456/1000000000000, 42188590232/1000000000000] : Fin 9 → ℚ) := by
    funext j
    fin_cases j
    · exact rounded_piece_2_0
    · exact rounded_piece_2_1
    · exact rounded_piece_2_2
    · exact rounded_piece_2_3
    · exact rounded_piece_2_4
    · exact rounded_piece_2_5
    · exact rounded_piece_2_6
    · exact rounded_piece_2_7
    · exact rounded_piece_2_8
  have hsum : (∑ j : Fin 9, roundedPiece 2 0 j) = (136874533394/1000000000000 : ℚ) := by
    rw [hpieces]
    norm_num [Fin.sum_univ_succ]
  unfold roundedEntry
  rw [hsum]
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_2_0
