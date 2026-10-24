import WR2ClassicalFifthInitialGridBlock000
import WR2ClassicalFifthInitialGridBlock001
import WR2ClassicalFifthInitialGridBlock002
import WR2ClassicalFifthInitialGridBlock003
import WR2ClassicalFifthInitialGridBlock004
import WR2ClassicalFifthInitialGridBlock005
import WR2ClassicalFifthInitialGridBlock006
import WR2ClassicalFifthInitialGridBlock007
import WR2ClassicalFifthInitialGridBlock008
import WR2ClassicalFifthInitialGridBlock009
import WR2ClassicalFifthInitialGridBlock010
import WR2ClassicalFifthInitialGridBlock011
import WR2ClassicalFifthInitialGridBlock012
import WR2ClassicalFifthInitialGridBlock013
import WR2ClassicalFifthInitialGridBlock014
import WR2ClassicalFifthInitialGridBlock015
import WR2ClassicalFifthInitialGridBlock016
import WR2ClassicalFifthInitialGridBlock017
import WR2ClassicalFifthInitialGridBlock018
import WR2ClassicalFifthInitialGridBlock019
import WR2ClassicalFifthInitialGridBlock020
import WR2ClassicalFifthInitialGridBlock021
import WR2ClassicalFifthInitialGridBlock022
import WR2ClassicalFifthInitialGridBlock023
import WR2ClassicalFifthInitialGridBlock024
import WR2ClassicalFifthInitialGridBlock025
import WR2ClassicalFifthInitialGridBlock026
import WR2ClassicalFifthInitialGridBlock027
import WR2ClassicalFifthInitialGridBlock028
import WR2ClassicalFifthInitialGridBlock029
import WR2ClassicalFifthInitialGridBlock030
import WR2ClassicalFifthInitialGridBlock031
import WR2ClassicalFifthInitialGridBlock032
import WR2ClassicalFifthInitialGridBlock033
import WR2ClassicalFifthInitialGridBlock034
import WR2ClassicalFifthInitialGridBlock035
import WR2ClassicalFifthInitialGridBlock036
import WR2ClassicalFifthInitialGridBlock037
import WR2ClassicalFifthInitialGridBlock038
import WR2ClassicalFifthInitialGridBlock039
import WR2ClassicalFifthInitialGridBlock040
import WR2ClassicalFifthInitialGridBlock041
import WR2ClassicalFifthInitialGridBlock042
import WR2ClassicalFifthInitialGridBlock043
import WR2ClassicalFifthInitialGridBlock044
import WR2ClassicalFifthInitialGridBlock045
import WR2ClassicalFifthInitialGridBlock046
import WR2ClassicalFifthInitialGridBlock047
import WR2ClassicalFifthInitialGridBlock048
import WR2ClassicalFifthInitialGridBlock049
import WR2ClassicalFifthInitialGridBlock050
import WR2ClassicalFifthInitialGridBlock051
import WR2ClassicalFifthInitialGridBlock052
import WR2ClassicalFifthInitialGridBlock053
import WR2ClassicalFifthInitialGridBlock054
import WR2ClassicalFifthInitialGridBlock055
import WR2ClassicalFifthInitialGridBlock056
import WR2ClassicalFifthInitialGridBlock057
import WR2ClassicalFifthInitialGridBlock058
import WR2ClassicalFifthInitialGridBlock059
import WR2ClassicalFifthInitialGridBlock060
import WR2ClassicalFifthInitialGridBlock061
import WR2ClassicalFifthInitialGridBlock062
import WR2ClassicalFifthInitialGridBlock063
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_initial_paid (i : ℕ) (hin : i < 1024) : initialPayment i ≤
    initialValue ((point lo 4 1024 i+point lo 4 1024 (i+1))/2) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 64 := by omega
  have hh (b : Fin 64) : initialPayment (16*b.val+i%16) ≤
      initialValue ((point lo 4 1024 (16*b.val+i%16)+point lo 4 1024 (16*b.val+i%16+1))/2) := by
    fin_cases b
    · exact initial_grid_block_000 ⟨i%16,hj⟩
    · exact initial_grid_block_001 ⟨i%16,hj⟩
    · exact initial_grid_block_002 ⟨i%16,hj⟩
    · exact initial_grid_block_003 ⟨i%16,hj⟩
    · exact initial_grid_block_004 ⟨i%16,hj⟩
    · exact initial_grid_block_005 ⟨i%16,hj⟩
    · exact initial_grid_block_006 ⟨i%16,hj⟩
    · exact initial_grid_block_007 ⟨i%16,hj⟩
    · exact initial_grid_block_008 ⟨i%16,hj⟩
    · exact initial_grid_block_009 ⟨i%16,hj⟩
    · exact initial_grid_block_010 ⟨i%16,hj⟩
    · exact initial_grid_block_011 ⟨i%16,hj⟩
    · exact initial_grid_block_012 ⟨i%16,hj⟩
    · exact initial_grid_block_013 ⟨i%16,hj⟩
    · exact initial_grid_block_014 ⟨i%16,hj⟩
    · exact initial_grid_block_015 ⟨i%16,hj⟩
    · exact initial_grid_block_016 ⟨i%16,hj⟩
    · exact initial_grid_block_017 ⟨i%16,hj⟩
    · exact initial_grid_block_018 ⟨i%16,hj⟩
    · exact initial_grid_block_019 ⟨i%16,hj⟩
    · exact initial_grid_block_020 ⟨i%16,hj⟩
    · exact initial_grid_block_021 ⟨i%16,hj⟩
    · exact initial_grid_block_022 ⟨i%16,hj⟩
    · exact initial_grid_block_023 ⟨i%16,hj⟩
    · exact initial_grid_block_024 ⟨i%16,hj⟩
    · exact initial_grid_block_025 ⟨i%16,hj⟩
    · exact initial_grid_block_026 ⟨i%16,hj⟩
    · exact initial_grid_block_027 ⟨i%16,hj⟩
    · exact initial_grid_block_028 ⟨i%16,hj⟩
    · exact initial_grid_block_029 ⟨i%16,hj⟩
    · exact initial_grid_block_030 ⟨i%16,hj⟩
    · exact initial_grid_block_031 ⟨i%16,hj⟩
    · exact initial_grid_block_032 ⟨i%16,hj⟩
    · exact initial_grid_block_033 ⟨i%16,hj⟩
    · exact initial_grid_block_034 ⟨i%16,hj⟩
    · exact initial_grid_block_035 ⟨i%16,hj⟩
    · exact initial_grid_block_036 ⟨i%16,hj⟩
    · exact initial_grid_block_037 ⟨i%16,hj⟩
    · exact initial_grid_block_038 ⟨i%16,hj⟩
    · exact initial_grid_block_039 ⟨i%16,hj⟩
    · exact initial_grid_block_040 ⟨i%16,hj⟩
    · exact initial_grid_block_041 ⟨i%16,hj⟩
    · exact initial_grid_block_042 ⟨i%16,hj⟩
    · exact initial_grid_block_043 ⟨i%16,hj⟩
    · exact initial_grid_block_044 ⟨i%16,hj⟩
    · exact initial_grid_block_045 ⟨i%16,hj⟩
    · exact initial_grid_block_046 ⟨i%16,hj⟩
    · exact initial_grid_block_047 ⟨i%16,hj⟩
    · exact initial_grid_block_048 ⟨i%16,hj⟩
    · exact initial_grid_block_049 ⟨i%16,hj⟩
    · exact initial_grid_block_050 ⟨i%16,hj⟩
    · exact initial_grid_block_051 ⟨i%16,hj⟩
    · exact initial_grid_block_052 ⟨i%16,hj⟩
    · exact initial_grid_block_053 ⟨i%16,hj⟩
    · exact initial_grid_block_054 ⟨i%16,hj⟩
    · exact initial_grid_block_055 ⟨i%16,hj⟩
    · exact initial_grid_block_056 ⟨i%16,hj⟩
    · exact initial_grid_block_057 ⟨i%16,hj⟩
    · exact initial_grid_block_058 ⟨i%16,hj⟩
    · exact initial_grid_block_059 ⟨i%16,hj⟩
    · exact initial_grid_block_060 ⟨i%16,hj⟩
    · exact initial_grid_block_061 ⟨i%16,hj⟩
    · exact initial_grid_block_062 ⟨i%16,hj⟩
    · exact initial_grid_block_063 ⟨i%16,hj⟩
  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_initial_paid
