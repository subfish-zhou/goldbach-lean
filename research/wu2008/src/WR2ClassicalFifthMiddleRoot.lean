import WR2ClassicalFifthMiddleGridBlock000
import WR2ClassicalFifthMiddleGridBlock001
import WR2ClassicalFifthMiddleGridBlock002
import WR2ClassicalFifthMiddleGridBlock003
import WR2ClassicalFifthMiddleGridBlock004
import WR2ClassicalFifthMiddleGridBlock005
import WR2ClassicalFifthMiddleGridBlock006
import WR2ClassicalFifthMiddleGridBlock007
import WR2ClassicalFifthMiddleGridBlock008
import WR2ClassicalFifthMiddleGridBlock009
import WR2ClassicalFifthMiddleGridBlock010
import WR2ClassicalFifthMiddleGridBlock011
import WR2ClassicalFifthMiddleGridBlock012
import WR2ClassicalFifthMiddleGridBlock013
import WR2ClassicalFifthMiddleGridBlock014
import WR2ClassicalFifthMiddleGridBlock015
import WR2ClassicalFifthMiddleGridBlock016
import WR2ClassicalFifthMiddleGridBlock017
import WR2ClassicalFifthMiddleGridBlock018
import WR2ClassicalFifthMiddleGridBlock019
import WR2ClassicalFifthMiddleGridBlock020
import WR2ClassicalFifthMiddleGridBlock021
import WR2ClassicalFifthMiddleGridBlock022
import WR2ClassicalFifthMiddleGridBlock023
import WR2ClassicalFifthMiddleGridBlock024
import WR2ClassicalFifthMiddleGridBlock025
import WR2ClassicalFifthMiddleGridBlock026
import WR2ClassicalFifthMiddleGridBlock027
import WR2ClassicalFifthMiddleGridBlock028
import WR2ClassicalFifthMiddleGridBlock029
import WR2ClassicalFifthMiddleGridBlock030
import WR2ClassicalFifthMiddleGridBlock031
import WR2ClassicalFifthMiddleGridBlock032
import WR2ClassicalFifthMiddleGridBlock033
import WR2ClassicalFifthMiddleGridBlock034
import WR2ClassicalFifthMiddleGridBlock035
import WR2ClassicalFifthMiddleGridBlock036
import WR2ClassicalFifthMiddleGridBlock037
import WR2ClassicalFifthMiddleGridBlock038
import WR2ClassicalFifthMiddleGridBlock039
import WR2ClassicalFifthMiddleGridBlock040
import WR2ClassicalFifthMiddleGridBlock041
import WR2ClassicalFifthMiddleGridBlock042
import WR2ClassicalFifthMiddleGridBlock043
import WR2ClassicalFifthMiddleGridBlock044
import WR2ClassicalFifthMiddleGridBlock045
import WR2ClassicalFifthMiddleGridBlock046
import WR2ClassicalFifthMiddleGridBlock047
import WR2ClassicalFifthMiddleGridBlock048
import WR2ClassicalFifthMiddleGridBlock049
import WR2ClassicalFifthMiddleGridBlock050
import WR2ClassicalFifthMiddleGridBlock051
import WR2ClassicalFifthMiddleGridBlock052
import WR2ClassicalFifthMiddleGridBlock053
import WR2ClassicalFifthMiddleGridBlock054
import WR2ClassicalFifthMiddleGridBlock055
import WR2ClassicalFifthMiddleGridBlock056
import WR2ClassicalFifthMiddleGridBlock057
import WR2ClassicalFifthMiddleGridBlock058
import WR2ClassicalFifthMiddleGridBlock059
import WR2ClassicalFifthMiddleGridBlock060
import WR2ClassicalFifthMiddleGridBlock061
import WR2ClassicalFifthMiddleGridBlock062
import WR2ClassicalFifthMiddleGridBlock063
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_middle_paid (i : ℕ) (hin : i < 1024) : middlePayment i ≤
    middleValue ((point 4 cut 1024 i+point 4 cut 1024 (i+1))/2) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 64 := by omega
  have hh (b : Fin 64) : middlePayment (16*b.val+i%16) ≤
      middleValue ((point 4 cut 1024 (16*b.val+i%16)+point 4 cut 1024 (16*b.val+i%16+1))/2) := by
    fin_cases b
    · exact middle_grid_block_000 ⟨i%16,hj⟩
    · exact middle_grid_block_001 ⟨i%16,hj⟩
    · exact middle_grid_block_002 ⟨i%16,hj⟩
    · exact middle_grid_block_003 ⟨i%16,hj⟩
    · exact middle_grid_block_004 ⟨i%16,hj⟩
    · exact middle_grid_block_005 ⟨i%16,hj⟩
    · exact middle_grid_block_006 ⟨i%16,hj⟩
    · exact middle_grid_block_007 ⟨i%16,hj⟩
    · exact middle_grid_block_008 ⟨i%16,hj⟩
    · exact middle_grid_block_009 ⟨i%16,hj⟩
    · exact middle_grid_block_010 ⟨i%16,hj⟩
    · exact middle_grid_block_011 ⟨i%16,hj⟩
    · exact middle_grid_block_012 ⟨i%16,hj⟩
    · exact middle_grid_block_013 ⟨i%16,hj⟩
    · exact middle_grid_block_014 ⟨i%16,hj⟩
    · exact middle_grid_block_015 ⟨i%16,hj⟩
    · exact middle_grid_block_016 ⟨i%16,hj⟩
    · exact middle_grid_block_017 ⟨i%16,hj⟩
    · exact middle_grid_block_018 ⟨i%16,hj⟩
    · exact middle_grid_block_019 ⟨i%16,hj⟩
    · exact middle_grid_block_020 ⟨i%16,hj⟩
    · exact middle_grid_block_021 ⟨i%16,hj⟩
    · exact middle_grid_block_022 ⟨i%16,hj⟩
    · exact middle_grid_block_023 ⟨i%16,hj⟩
    · exact middle_grid_block_024 ⟨i%16,hj⟩
    · exact middle_grid_block_025 ⟨i%16,hj⟩
    · exact middle_grid_block_026 ⟨i%16,hj⟩
    · exact middle_grid_block_027 ⟨i%16,hj⟩
    · exact middle_grid_block_028 ⟨i%16,hj⟩
    · exact middle_grid_block_029 ⟨i%16,hj⟩
    · exact middle_grid_block_030 ⟨i%16,hj⟩
    · exact middle_grid_block_031 ⟨i%16,hj⟩
    · exact middle_grid_block_032 ⟨i%16,hj⟩
    · exact middle_grid_block_033 ⟨i%16,hj⟩
    · exact middle_grid_block_034 ⟨i%16,hj⟩
    · exact middle_grid_block_035 ⟨i%16,hj⟩
    · exact middle_grid_block_036 ⟨i%16,hj⟩
    · exact middle_grid_block_037 ⟨i%16,hj⟩
    · exact middle_grid_block_038 ⟨i%16,hj⟩
    · exact middle_grid_block_039 ⟨i%16,hj⟩
    · exact middle_grid_block_040 ⟨i%16,hj⟩
    · exact middle_grid_block_041 ⟨i%16,hj⟩
    · exact middle_grid_block_042 ⟨i%16,hj⟩
    · exact middle_grid_block_043 ⟨i%16,hj⟩
    · exact middle_grid_block_044 ⟨i%16,hj⟩
    · exact middle_grid_block_045 ⟨i%16,hj⟩
    · exact middle_grid_block_046 ⟨i%16,hj⟩
    · exact middle_grid_block_047 ⟨i%16,hj⟩
    · exact middle_grid_block_048 ⟨i%16,hj⟩
    · exact middle_grid_block_049 ⟨i%16,hj⟩
    · exact middle_grid_block_050 ⟨i%16,hj⟩
    · exact middle_grid_block_051 ⟨i%16,hj⟩
    · exact middle_grid_block_052 ⟨i%16,hj⟩
    · exact middle_grid_block_053 ⟨i%16,hj⟩
    · exact middle_grid_block_054 ⟨i%16,hj⟩
    · exact middle_grid_block_055 ⟨i%16,hj⟩
    · exact middle_grid_block_056 ⟨i%16,hj⟩
    · exact middle_grid_block_057 ⟨i%16,hj⟩
    · exact middle_grid_block_058 ⟨i%16,hj⟩
    · exact middle_grid_block_059 ⟨i%16,hj⟩
    · exact middle_grid_block_060 ⟨i%16,hj⟩
    · exact middle_grid_block_061 ⟨i%16,hj⟩
    · exact middle_grid_block_062 ⟨i%16,hj⟩
    · exact middle_grid_block_063 ⟨i%16,hj⟩
  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_middle_paid
