import WR2ClassicalFifthTerminalGridBlock000
import WR2ClassicalFifthTerminalGridBlock001
import WR2ClassicalFifthTerminalGridBlock002
import WR2ClassicalFifthTerminalGridBlock003
import WR2ClassicalFifthTerminalGridBlock004
import WR2ClassicalFifthTerminalGridBlock005
import WR2ClassicalFifthTerminalGridBlock006
import WR2ClassicalFifthTerminalGridBlock007
import WR2ClassicalFifthTerminalGridBlock008
import WR2ClassicalFifthTerminalGridBlock009
import WR2ClassicalFifthTerminalGridBlock010
import WR2ClassicalFifthTerminalGridBlock011
import WR2ClassicalFifthTerminalGridBlock012
import WR2ClassicalFifthTerminalGridBlock013
import WR2ClassicalFifthTerminalGridBlock014
import WR2ClassicalFifthTerminalGridBlock015
import WR2ClassicalFifthTerminalGridBlock016
import WR2ClassicalFifthTerminalGridBlock017
import WR2ClassicalFifthTerminalGridBlock018
import WR2ClassicalFifthTerminalGridBlock019
import WR2ClassicalFifthTerminalGridBlock020
import WR2ClassicalFifthTerminalGridBlock021
import WR2ClassicalFifthTerminalGridBlock022
import WR2ClassicalFifthTerminalGridBlock023
import WR2ClassicalFifthTerminalGridBlock024
import WR2ClassicalFifthTerminalGridBlock025
import WR2ClassicalFifthTerminalGridBlock026
import WR2ClassicalFifthTerminalGridBlock027
import WR2ClassicalFifthTerminalGridBlock028
import WR2ClassicalFifthTerminalGridBlock029
import WR2ClassicalFifthTerminalGridBlock030
import WR2ClassicalFifthTerminalGridBlock031
import WR2ClassicalFifthTerminalGridBlock032
import WR2ClassicalFifthTerminalGridBlock033
import WR2ClassicalFifthTerminalGridBlock034
import WR2ClassicalFifthTerminalGridBlock035
import WR2ClassicalFifthTerminalGridBlock036
import WR2ClassicalFifthTerminalGridBlock037
import WR2ClassicalFifthTerminalGridBlock038
import WR2ClassicalFifthTerminalGridBlock039
import WR2ClassicalFifthTerminalGridBlock040
import WR2ClassicalFifthTerminalGridBlock041
import WR2ClassicalFifthTerminalGridBlock042
import WR2ClassicalFifthTerminalGridBlock043
import WR2ClassicalFifthTerminalGridBlock044
import WR2ClassicalFifthTerminalGridBlock045
import WR2ClassicalFifthTerminalGridBlock046
import WR2ClassicalFifthTerminalGridBlock047
import WR2ClassicalFifthTerminalGridBlock048
import WR2ClassicalFifthTerminalGridBlock049
import WR2ClassicalFifthTerminalGridBlock050
import WR2ClassicalFifthTerminalGridBlock051
import WR2ClassicalFifthTerminalGridBlock052
import WR2ClassicalFifthTerminalGridBlock053
import WR2ClassicalFifthTerminalGridBlock054
import WR2ClassicalFifthTerminalGridBlock055
import WR2ClassicalFifthTerminalGridBlock056
import WR2ClassicalFifthTerminalGridBlock057
import WR2ClassicalFifthTerminalGridBlock058
import WR2ClassicalFifthTerminalGridBlock059
import WR2ClassicalFifthTerminalGridBlock060
import WR2ClassicalFifthTerminalGridBlock061
import WR2ClassicalFifthTerminalGridBlock062
import WR2ClassicalFifthTerminalGridBlock063
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_terminal_paid (i : ℕ) (hin : i < 1024) : terminalPayment i ≤
    terminalValue ((point cut hi 1024 i+point cut hi 1024 (i+1))/2) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 64 := by omega
  have hh (b : Fin 64) : terminalPayment (16*b.val+i%16) ≤
      terminalValue ((point cut hi 1024 (16*b.val+i%16)+point cut hi 1024 (16*b.val+i%16+1))/2) := by
    fin_cases b
    · exact terminal_grid_block_000 ⟨i%16,hj⟩
    · exact terminal_grid_block_001 ⟨i%16,hj⟩
    · exact terminal_grid_block_002 ⟨i%16,hj⟩
    · exact terminal_grid_block_003 ⟨i%16,hj⟩
    · exact terminal_grid_block_004 ⟨i%16,hj⟩
    · exact terminal_grid_block_005 ⟨i%16,hj⟩
    · exact terminal_grid_block_006 ⟨i%16,hj⟩
    · exact terminal_grid_block_007 ⟨i%16,hj⟩
    · exact terminal_grid_block_008 ⟨i%16,hj⟩
    · exact terminal_grid_block_009 ⟨i%16,hj⟩
    · exact terminal_grid_block_010 ⟨i%16,hj⟩
    · exact terminal_grid_block_011 ⟨i%16,hj⟩
    · exact terminal_grid_block_012 ⟨i%16,hj⟩
    · exact terminal_grid_block_013 ⟨i%16,hj⟩
    · exact terminal_grid_block_014 ⟨i%16,hj⟩
    · exact terminal_grid_block_015 ⟨i%16,hj⟩
    · exact terminal_grid_block_016 ⟨i%16,hj⟩
    · exact terminal_grid_block_017 ⟨i%16,hj⟩
    · exact terminal_grid_block_018 ⟨i%16,hj⟩
    · exact terminal_grid_block_019 ⟨i%16,hj⟩
    · exact terminal_grid_block_020 ⟨i%16,hj⟩
    · exact terminal_grid_block_021 ⟨i%16,hj⟩
    · exact terminal_grid_block_022 ⟨i%16,hj⟩
    · exact terminal_grid_block_023 ⟨i%16,hj⟩
    · exact terminal_grid_block_024 ⟨i%16,hj⟩
    · exact terminal_grid_block_025 ⟨i%16,hj⟩
    · exact terminal_grid_block_026 ⟨i%16,hj⟩
    · exact terminal_grid_block_027 ⟨i%16,hj⟩
    · exact terminal_grid_block_028 ⟨i%16,hj⟩
    · exact terminal_grid_block_029 ⟨i%16,hj⟩
    · exact terminal_grid_block_030 ⟨i%16,hj⟩
    · exact terminal_grid_block_031 ⟨i%16,hj⟩
    · exact terminal_grid_block_032 ⟨i%16,hj⟩
    · exact terminal_grid_block_033 ⟨i%16,hj⟩
    · exact terminal_grid_block_034 ⟨i%16,hj⟩
    · exact terminal_grid_block_035 ⟨i%16,hj⟩
    · exact terminal_grid_block_036 ⟨i%16,hj⟩
    · exact terminal_grid_block_037 ⟨i%16,hj⟩
    · exact terminal_grid_block_038 ⟨i%16,hj⟩
    · exact terminal_grid_block_039 ⟨i%16,hj⟩
    · exact terminal_grid_block_040 ⟨i%16,hj⟩
    · exact terminal_grid_block_041 ⟨i%16,hj⟩
    · exact terminal_grid_block_042 ⟨i%16,hj⟩
    · exact terminal_grid_block_043 ⟨i%16,hj⟩
    · exact terminal_grid_block_044 ⟨i%16,hj⟩
    · exact terminal_grid_block_045 ⟨i%16,hj⟩
    · exact terminal_grid_block_046 ⟨i%16,hj⟩
    · exact terminal_grid_block_047 ⟨i%16,hj⟩
    · exact terminal_grid_block_048 ⟨i%16,hj⟩
    · exact terminal_grid_block_049 ⟨i%16,hj⟩
    · exact terminal_grid_block_050 ⟨i%16,hj⟩
    · exact terminal_grid_block_051 ⟨i%16,hj⟩
    · exact terminal_grid_block_052 ⟨i%16,hj⟩
    · exact terminal_grid_block_053 ⟨i%16,hj⟩
    · exact terminal_grid_block_054 ⟨i%16,hj⟩
    · exact terminal_grid_block_055 ⟨i%16,hj⟩
    · exact terminal_grid_block_056 ⟨i%16,hj⟩
    · exact terminal_grid_block_057 ⟨i%16,hj⟩
    · exact terminal_grid_block_058 ⟨i%16,hj⟩
    · exact terminal_grid_block_059 ⟨i%16,hj⟩
    · exact terminal_grid_block_060 ⟨i%16,hj⟩
    · exact terminal_grid_block_061 ⟨i%16,hj⟩
    · exact terminal_grid_block_062 ⟨i%16,hj⟩
    · exact terminal_grid_block_063 ⟨i%16,hj⟩
  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_terminal_paid
