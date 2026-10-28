import Mathlib.Tactic.FinCases
import WR2ClassicalFourthBPayBatch000
import WR2ClassicalFourthBPayBatch001
import WR2ClassicalFourthBPayBatch002
import WR2ClassicalFourthBPayBatch003
import WR2ClassicalFourthBPayBatch004
import WR2ClassicalFourthBPayBatch005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_BPay (i : ℕ) (hi : i < 10540) : BPay (i) := by
  have hj : i%256 < 256 := Nat.mod_lt _ (by norm_num)
  have hb : i/256 < 42 := by omega
  have hh (b : Fin 42) : 256*b.val+i%256 < 10540 → BPay (256*b.val+i%256) := by
    fin_cases b
    · exact BPay_block_000 ⟨i%256,hj⟩
    · exact BPay_block_001 ⟨i%256,hj⟩
    · exact BPay_block_002 ⟨i%256,hj⟩
    · exact BPay_block_003 ⟨i%256,hj⟩
    · exact BPay_block_004 ⟨i%256,hj⟩
    · exact BPay_block_005 ⟨i%256,hj⟩
    · exact BPay_block_006 ⟨i%256,hj⟩
    · exact BPay_block_007 ⟨i%256,hj⟩
    · exact BPay_block_008 ⟨i%256,hj⟩
    · exact BPay_block_009 ⟨i%256,hj⟩
    · exact BPay_block_010 ⟨i%256,hj⟩
    · exact BPay_block_011 ⟨i%256,hj⟩
    · exact BPay_block_012 ⟨i%256,hj⟩
    · exact BPay_block_013 ⟨i%256,hj⟩
    · exact BPay_block_014 ⟨i%256,hj⟩
    · exact BPay_block_015 ⟨i%256,hj⟩
    · exact BPay_block_016 ⟨i%256,hj⟩
    · exact BPay_block_017 ⟨i%256,hj⟩
    · exact BPay_block_018 ⟨i%256,hj⟩
    · exact BPay_block_019 ⟨i%256,hj⟩
    · exact BPay_block_020 ⟨i%256,hj⟩
    · exact BPay_block_021 ⟨i%256,hj⟩
    · exact BPay_block_022 ⟨i%256,hj⟩
    · exact BPay_block_023 ⟨i%256,hj⟩
    · exact BPay_block_024 ⟨i%256,hj⟩
    · exact BPay_block_025 ⟨i%256,hj⟩
    · exact BPay_block_026 ⟨i%256,hj⟩
    · exact BPay_block_027 ⟨i%256,hj⟩
    · exact BPay_block_028 ⟨i%256,hj⟩
    · exact BPay_block_029 ⟨i%256,hj⟩
    · exact BPay_block_030 ⟨i%256,hj⟩
    · exact BPay_block_031 ⟨i%256,hj⟩
    · exact BPay_block_032 ⟨i%256,hj⟩
    · exact BPay_block_033 ⟨i%256,hj⟩
    · exact BPay_block_034 ⟨i%256,hj⟩
    · exact BPay_block_035 ⟨i%256,hj⟩
    · exact BPay_block_036 ⟨i%256,hj⟩
    · exact BPay_block_037 ⟨i%256,hj⟩
    · exact BPay_block_038 ⟨i%256,hj⟩
    · exact BPay_block_039 ⟨i%256,hj⟩
    · exact BPay_block_040 ⟨i%256,hj⟩
    · exact BPay_block_041 ⟨i%256,hj⟩
  have he : 256*(i/256)+i%256=i := by omega
  have h := hh ⟨i/256,hb⟩ (by change 256*(i/256)+i%256 < 10540; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_BPay
