import WR2ClassicalFourthBlockCPay000
import WR2ClassicalFourthBlockCPay001
import WR2ClassicalFourthBlockCPay002
import WR2ClassicalFourthBlockCPay003
import WR2ClassicalFourthBlockCPay004
import WR2ClassicalFourthBlockCPay005
import WR2ClassicalFourthBlockCPay006
import WR2ClassicalFourthBlockCPay007
import WR2ClassicalFourthBlockCPay008
import WR2ClassicalFourthBlockCPay009
import WR2ClassicalFourthBlockCPay010
import WR2ClassicalFourthBlockCPay011
import WR2ClassicalFourthBlockCPay012
import WR2ClassicalFourthBlockCPay013
import WR2ClassicalFourthBlockCPay014
import WR2ClassicalFourthBlockCPay015
import WR2ClassicalFourthBlockCPay016
import WR2ClassicalFourthBlockCPay017
import WR2ClassicalFourthBlockCPay018
import WR2ClassicalFourthBlockCPay019
import WR2ClassicalFourthBlockCPay020
import WR2ClassicalFourthBlockCPay021
import WR2ClassicalFourthBlockCPay022
import WR2ClassicalFourthBlockCPay023
import WR2ClassicalFourthBlockCPay024
import WR2ClassicalFourthBlockCPay025
import WR2ClassicalFourthBlockCPay026
import WR2ClassicalFourthBlockCPay027
import WR2ClassicalFourthBlockCPay028
import WR2ClassicalFourthBlockCPay029
import WR2ClassicalFourthBlockCPay030
import WR2ClassicalFourthBlockCPay031
import WR2ClassicalFourthBlockCPay032
import WR2ClassicalFourthBlockCPay033
import WR2ClassicalFourthBlockCPay034
import WR2ClassicalFourthBlockCPay035
import WR2ClassicalFourthBlockCPay036
import WR2ClassicalFourthBlockCPay037
import WR2ClassicalFourthBlockCPay038
import WR2ClassicalFourthBlockCPay039
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_CPay (i : ℕ) (hi : i < 2540) : CPay (i) := by
  have hj : i%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : i/64 < 40 := by omega
  have hh (b : Fin 40) : 64*b.val+i%64 < 2540 → CPay (64*b.val+i%64) := by
    fin_cases b
    · exact CPay_block_000 ⟨i%64,hj⟩
    · exact CPay_block_001 ⟨i%64,hj⟩
    · exact CPay_block_002 ⟨i%64,hj⟩
    · exact CPay_block_003 ⟨i%64,hj⟩
    · exact CPay_block_004 ⟨i%64,hj⟩
    · exact CPay_block_005 ⟨i%64,hj⟩
    · exact CPay_block_006 ⟨i%64,hj⟩
    · exact CPay_block_007 ⟨i%64,hj⟩
    · exact CPay_block_008 ⟨i%64,hj⟩
    · exact CPay_block_009 ⟨i%64,hj⟩
    · exact CPay_block_010 ⟨i%64,hj⟩
    · exact CPay_block_011 ⟨i%64,hj⟩
    · exact CPay_block_012 ⟨i%64,hj⟩
    · exact CPay_block_013 ⟨i%64,hj⟩
    · exact CPay_block_014 ⟨i%64,hj⟩
    · exact CPay_block_015 ⟨i%64,hj⟩
    · exact CPay_block_016 ⟨i%64,hj⟩
    · exact CPay_block_017 ⟨i%64,hj⟩
    · exact CPay_block_018 ⟨i%64,hj⟩
    · exact CPay_block_019 ⟨i%64,hj⟩
    · exact CPay_block_020 ⟨i%64,hj⟩
    · exact CPay_block_021 ⟨i%64,hj⟩
    · exact CPay_block_022 ⟨i%64,hj⟩
    · exact CPay_block_023 ⟨i%64,hj⟩
    · exact CPay_block_024 ⟨i%64,hj⟩
    · exact CPay_block_025 ⟨i%64,hj⟩
    · exact CPay_block_026 ⟨i%64,hj⟩
    · exact CPay_block_027 ⟨i%64,hj⟩
    · exact CPay_block_028 ⟨i%64,hj⟩
    · exact CPay_block_029 ⟨i%64,hj⟩
    · exact CPay_block_030 ⟨i%64,hj⟩
    · exact CPay_block_031 ⟨i%64,hj⟩
    · exact CPay_block_032 ⟨i%64,hj⟩
    · exact CPay_block_033 ⟨i%64,hj⟩
    · exact CPay_block_034 ⟨i%64,hj⟩
    · exact CPay_block_035 ⟨i%64,hj⟩
    · exact CPay_block_036 ⟨i%64,hj⟩
    · exact CPay_block_037 ⟨i%64,hj⟩
    · exact CPay_block_038 ⟨i%64,hj⟩
    · exact CPay_block_039 ⟨i%64,hj⟩
  have he : 64*(i/64)+i%64=i := by omega
  have h := hh ⟨i/64,hb⟩ (by change 64*(i/64)+i%64 < 2540; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_CPay
