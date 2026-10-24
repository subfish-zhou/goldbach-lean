import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import WR2XiRoundedPiece00
import WR2XiRoundedPiece01
import WR2XiRoundedPiece02
import WR2XiRoundedPiece03
import WR2XiRoundedPiece04
import WR2XiRoundedPiece05
import WR2XiRoundedPiece06
import WR2XiRoundedPiece07
import WR2XiRoundedPiece08
namespace Xi2RationalMixed
open Xi2RationalTop
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_0_0 : target 0 0 + (if (0 : Fin 9) = 0 then debit 0 else 0) ≤ entry 0 0 := by
  apply le_trans (b := roundedEntry 0 0) _ (roundedEntry_le 0 0)
  have hpieces : roundedPiece 0 0 = (![0/1000000000000, 4186432559/1000000000000, 12676668562/1000000000000, 24779937405/1000000000000, 37455072394/1000000000000, 11177446078/1000000000000, 713570004/1000000000000, 5128015447/1000000000000, 42960449698/1000000000000] : Fin 9 → ℚ) := by
    funext j
    fin_cases j
    · exact rounded_piece_0_0
    · exact rounded_piece_0_1
    · exact rounded_piece_0_2
    · exact rounded_piece_0_3
    · exact rounded_piece_0_4
    · exact rounded_piece_0_5
    · exact rounded_piece_0_6
    · exact rounded_piece_0_7
    · exact rounded_piece_0_8
  have hsum : (∑ j : Fin 9, roundedPiece 0 0 j) = (139077592147/1000000000000 : ℚ) := by
    rw [hpieces]
    norm_num [Fin.sum_univ_succ]
  unfold roundedEntry
  rw [hsum]
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_0_0
