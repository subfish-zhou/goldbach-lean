import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import WR2XiRoundedPiece30
import WR2XiRoundedPiece31
import WR2XiRoundedPiece32
import WR2XiRoundedPiece33
import WR2XiRoundedPiece34
import WR2XiRoundedPiece35
import WR2XiRoundedPiece36
import WR2XiRoundedPiece37
import WR2XiRoundedPiece38
namespace Xi2RationalMixed
open Xi2RationalTop
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_3_0 : target 3 0 + (if (0 : Fin 9) = 0 then debit 3 else 0) ≤ entry 3 0 := by
  apply le_trans (b := roundedEntry 3 0) _ (roundedEntry_le 3 0)
  have hpieces : roundedPiece 3 0 = (![16418346885/1000000000000, 4317362270/1000000000000, 23869018264/1000000000000, 23869018264/1000000000000, 29851639280/1000000000000, 4070336505/1000000000000, 3897936623/1000000000000, 5335347061/1000000000000, 27838343453/1000000000000] : Fin 9 → ℚ) := by
    funext j
    fin_cases j
    · exact rounded_piece_3_0
    · exact rounded_piece_3_1
    · exact rounded_piece_3_2
    · exact rounded_piece_3_3
    · exact rounded_piece_3_4
    · exact rounded_piece_3_5
    · exact rounded_piece_3_6
    · exact rounded_piece_3_7
    · exact rounded_piece_3_8
  have hsum : (∑ j : Fin 9, roundedPiece 3 0 j) = (139467348605/1000000000000 : ℚ) := by
    rw [hpieces]
    norm_num [Fin.sum_univ_succ]
  unfold roundedEntry
  rw [hsum]
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_3_0
