import WR2ClassicalFourthBlockDPay000
import WR2ClassicalFourthBlockDPay001
import WR2ClassicalFourthBlockDPay002
import WR2ClassicalFourthBlockDPay003
import WR2ClassicalFourthBlockDPay004
import WR2ClassicalFourthBlockDPay005
import WR2ClassicalFourthBlockDPay006
import WR2ClassicalFourthBlockDPay007
import WR2ClassicalFourthBlockDPay008
import WR2ClassicalFourthBlockDPay009
import WR2ClassicalFourthBlockDPay010
import WR2ClassicalFourthBlockDPay011
import WR2ClassicalFourthBlockDPay012
import WR2ClassicalFourthBlockDPay013
import WR2ClassicalFourthBlockDPay014
import WR2ClassicalFourthBlockDPay015
import WR2ClassicalFourthBlockDPay016
import WR2ClassicalFourthBlockDPay017
import WR2ClassicalFourthBlockDPay018
import WR2ClassicalFourthBlockDPay019
import WR2ClassicalFourthBlockDPay020
import WR2ClassicalFourthBlockDPay021
import WR2ClassicalFourthBlockDPay022
import WR2ClassicalFourthBlockDPay023
import WR2ClassicalFourthBlockDPay024
import WR2ClassicalFourthBlockDPay025
import WR2ClassicalFourthBlockDPay026
import WR2ClassicalFourthBlockDPay027
import WR2ClassicalFourthBlockDPay028
import WR2ClassicalFourthBlockDPay029
import WR2ClassicalFourthBlockDPay030
import WR2ClassicalFourthBlockDPay031
import WR2ClassicalFourthBlockDPay032
import WR2ClassicalFourthBlockDPay033
import WR2ClassicalFourthBlockDPay034
import WR2ClassicalFourthBlockDPay035
import WR2ClassicalFourthBlockDPay036
import WR2ClassicalFourthBlockDPay037
import WR2ClassicalFourthBlockDPay038
import WR2ClassicalFourthBlockDPay039
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_DPay (i : ℕ) (hi : i < 2540) : DPay (i) := by
  have hj : i%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : i/64 < 40 := by omega
  have hh (b : Fin 40) : 64*b.val+i%64 < 2540 → DPay (64*b.val+i%64) := by
    fin_cases b
    · exact DPay_block_000 ⟨i%64,hj⟩
    · exact DPay_block_001 ⟨i%64,hj⟩
    · exact DPay_block_002 ⟨i%64,hj⟩
    · exact DPay_block_003 ⟨i%64,hj⟩
    · exact DPay_block_004 ⟨i%64,hj⟩
    · exact DPay_block_005 ⟨i%64,hj⟩
    · exact DPay_block_006 ⟨i%64,hj⟩
    · exact DPay_block_007 ⟨i%64,hj⟩
    · exact DPay_block_008 ⟨i%64,hj⟩
    · exact DPay_block_009 ⟨i%64,hj⟩
    · exact DPay_block_010 ⟨i%64,hj⟩
    · exact DPay_block_011 ⟨i%64,hj⟩
    · exact DPay_block_012 ⟨i%64,hj⟩
    · exact DPay_block_013 ⟨i%64,hj⟩
    · exact DPay_block_014 ⟨i%64,hj⟩
    · exact DPay_block_015 ⟨i%64,hj⟩
    · exact DPay_block_016 ⟨i%64,hj⟩
    · exact DPay_block_017 ⟨i%64,hj⟩
    · exact DPay_block_018 ⟨i%64,hj⟩
    · exact DPay_block_019 ⟨i%64,hj⟩
    · exact DPay_block_020 ⟨i%64,hj⟩
    · exact DPay_block_021 ⟨i%64,hj⟩
    · exact DPay_block_022 ⟨i%64,hj⟩
    · exact DPay_block_023 ⟨i%64,hj⟩
    · exact DPay_block_024 ⟨i%64,hj⟩
    · exact DPay_block_025 ⟨i%64,hj⟩
    · exact DPay_block_026 ⟨i%64,hj⟩
    · exact DPay_block_027 ⟨i%64,hj⟩
    · exact DPay_block_028 ⟨i%64,hj⟩
    · exact DPay_block_029 ⟨i%64,hj⟩
    · exact DPay_block_030 ⟨i%64,hj⟩
    · exact DPay_block_031 ⟨i%64,hj⟩
    · exact DPay_block_032 ⟨i%64,hj⟩
    · exact DPay_block_033 ⟨i%64,hj⟩
    · exact DPay_block_034 ⟨i%64,hj⟩
    · exact DPay_block_035 ⟨i%64,hj⟩
    · exact DPay_block_036 ⟨i%64,hj⟩
    · exact DPay_block_037 ⟨i%64,hj⟩
    · exact DPay_block_038 ⟨i%64,hj⟩
    · exact DPay_block_039 ⟨i%64,hj⟩
  have he : 64*(i/64)+i%64=i := by omega
  have h := hh ⟨i/64,hb⟩ (by change 64*(i/64)+i%64 < 2540; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_DPay
