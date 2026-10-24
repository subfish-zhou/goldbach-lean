import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import WR2XiRoundedPiece10
import WR2XiRoundedPiece11
import WR2XiRoundedPiece12
import WR2XiRoundedPiece13
import WR2XiRoundedPiece14
import WR2XiRoundedPiece15
import WR2XiRoundedPiece16
import WR2XiRoundedPiece17
import WR2XiRoundedPiece18
namespace Xi2RationalMixed
open Xi2RationalTop
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_1_0 : target 1 0 + (if (0 : Fin 9) = 0 then debit 1 else 0) ≤ entry 1 0 := by
  apply le_trans (b := roundedEntry 1 0) _ (roundedEntry_le 1 0)
  have hpieces : roundedPiece 1 0 = (![0/1000000000000, 4617643857/1000000000000, 14471519896/1000000000000, 20577409434/1000000000000, 37551635791/1000000000000, 10224760548/1000000000000, 1385111694/1000000000000, 5672633031/1000000000000, 43374209809/1000000000000] : Fin 9 → ℚ) := by
    funext j
    fin_cases j
    · exact rounded_piece_1_0
    · exact rounded_piece_1_1
    · exact rounded_piece_1_2
    · exact rounded_piece_1_3
    · exact rounded_piece_1_4
    · exact rounded_piece_1_5
    · exact rounded_piece_1_6
    · exact rounded_piece_1_7
    · exact rounded_piece_1_8
  have hsum : (∑ j : Fin 9, roundedPiece 1 0 j) = (137874924060/1000000000000 : ℚ) := by
    rw [hpieces]
    norm_num [Fin.sum_univ_succ]
  unfold roundedEntry
  rw [hsum]
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_1_0
