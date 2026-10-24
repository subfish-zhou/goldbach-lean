import WR2ClassicalEighthCorrectionGridBlock000
import WR2ClassicalEighthCorrectionGridBlock001
import WR2ClassicalEighthCorrectionGridBlock002
import WR2ClassicalEighthCorrectionGridBlock003
import WR2ClassicalEighthCorrectionGridBlock004
import WR2ClassicalEighthCorrectionGridBlock005
import WR2ClassicalEighthCorrectionGridBlock006
import WR2ClassicalEighthCorrectionGridBlock007
import WR2ClassicalEighthCorrectionGridBlock008
import WR2ClassicalEighthCorrectionGridBlock009
import WR2ClassicalEighthCorrectionGridBlock010
import WR2ClassicalEighthCorrectionGridBlock011
import WR2ClassicalEighthCorrectionGridBlock012
import WR2ClassicalEighthCorrectionGridBlock013
import WR2ClassicalEighthCorrectionGridBlock014
import WR2ClassicalEighthCorrectionGridBlock015
import WR2ClassicalEighthCorrectionGridBlock016
import WR2ClassicalEighthCorrectionGridBlock017
import WR2ClassicalEighthCorrectionGridBlock018
import WR2ClassicalEighthCorrectionGridBlock019
import WR2ClassicalEighthCorrectionGridBlock020
import WR2ClassicalEighthCorrectionGridBlock021
import WR2ClassicalEighthCorrectionGridBlock022
import WR2ClassicalEighthCorrectionGridBlock023
import WR2ClassicalEighthCorrectionGridBlock024
import WR2ClassicalEighthCorrectionGridBlock025
import WR2ClassicalEighthCorrectionGridBlock026
import WR2ClassicalEighthCorrectionGridBlock027
import WR2ClassicalEighthCorrectionGridBlock028
import WR2ClassicalEighthCorrectionGridBlock029
import WR2ClassicalEighthCorrectionGridBlock030
import WR2ClassicalEighthCorrectionGridBlock031
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
open Finset
set_option maxHeartbeats 4000000 in
theorem all_paid (i : ℕ) (hi : i < 512) : step*payment (i) ≤ cellPayment (point (i)) (point ((i)+1)) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 32 := by omega
  have hh (b : Fin 32) : step*payment (16*b.val+i%16) ≤ cellPayment (point (16*b.val+i%16)) (point ((16*b.val+i%16)+1)) := by
    fin_cases b
    · exact grid_block_000 ⟨i%16,hj⟩
    · exact grid_block_001 ⟨i%16,hj⟩
    · exact grid_block_002 ⟨i%16,hj⟩
    · exact grid_block_003 ⟨i%16,hj⟩
    · exact grid_block_004 ⟨i%16,hj⟩
    · exact grid_block_005 ⟨i%16,hj⟩
    · exact grid_block_006 ⟨i%16,hj⟩
    · exact grid_block_007 ⟨i%16,hj⟩
    · exact grid_block_008 ⟨i%16,hj⟩
    · exact grid_block_009 ⟨i%16,hj⟩
    · exact grid_block_010 ⟨i%16,hj⟩
    · exact grid_block_011 ⟨i%16,hj⟩
    · exact grid_block_012 ⟨i%16,hj⟩
    · exact grid_block_013 ⟨i%16,hj⟩
    · exact grid_block_014 ⟨i%16,hj⟩
    · exact grid_block_015 ⟨i%16,hj⟩
    · exact grid_block_016 ⟨i%16,hj⟩
    · exact grid_block_017 ⟨i%16,hj⟩
    · exact grid_block_018 ⟨i%16,hj⟩
    · exact grid_block_019 ⟨i%16,hj⟩
    · exact grid_block_020 ⟨i%16,hj⟩
    · exact grid_block_021 ⟨i%16,hj⟩
    · exact grid_block_022 ⟨i%16,hj⟩
    · exact grid_block_023 ⟨i%16,hj⟩
    · exact grid_block_024 ⟨i%16,hj⟩
    · exact grid_block_025 ⟨i%16,hj⟩
    · exact grid_block_026 ⟨i%16,hj⟩
    · exact grid_block_027 ⟨i%16,hj⟩
    · exact grid_block_028 ⟨i%16,hj⟩
    · exact grid_block_029 ⟨i%16,hj⟩
    · exact grid_block_030 ⟨i%16,hj⟩
    · exact grid_block_031 ⟨i%16,hj⟩
  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
theorem correction_lower : (194378:ℝ)/10000000 ≤ 8*(U8CanonicalMother.L-U8CanonicalMother.I) := by
  apply le_trans _ (uniform_lower payment all_paid)
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.correction_lower
