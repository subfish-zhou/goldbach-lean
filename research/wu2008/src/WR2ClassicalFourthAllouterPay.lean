import Mathlib.Tactic.FinCases
import WR2ClassicalFourthouterPayBatch000
import WR2ClassicalFourthouterPayBatch001
import WR2ClassicalFourthouterPayBatch002
import WR2ClassicalFourthouterPayBatch003
import WR2ClassicalFourthouterPayBatch004
import WR2ClassicalFourthouterPayBatch005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_outerPay (i : ℕ) (hi : i < 10540) : OuterPay (i) := by
  have hj : i%256 < 256 := Nat.mod_lt _ (by norm_num)
  have hb : i/256 < 42 := by omega
  have hh (b : Fin 42) : 256*b.val+i%256 < 10540 → OuterPay (256*b.val+i%256) := by
    fin_cases b
    · exact outerPay_block_000 ⟨i%256,hj⟩
    · exact outerPay_block_001 ⟨i%256,hj⟩
    · exact outerPay_block_002 ⟨i%256,hj⟩
    · exact outerPay_block_003 ⟨i%256,hj⟩
    · exact outerPay_block_004 ⟨i%256,hj⟩
    · exact outerPay_block_005 ⟨i%256,hj⟩
    · exact outerPay_block_006 ⟨i%256,hj⟩
    · exact outerPay_block_007 ⟨i%256,hj⟩
    · exact outerPay_block_008 ⟨i%256,hj⟩
    · exact outerPay_block_009 ⟨i%256,hj⟩
    · exact outerPay_block_010 ⟨i%256,hj⟩
    · exact outerPay_block_011 ⟨i%256,hj⟩
    · exact outerPay_block_012 ⟨i%256,hj⟩
    · exact outerPay_block_013 ⟨i%256,hj⟩
    · exact outerPay_block_014 ⟨i%256,hj⟩
    · exact outerPay_block_015 ⟨i%256,hj⟩
    · exact outerPay_block_016 ⟨i%256,hj⟩
    · exact outerPay_block_017 ⟨i%256,hj⟩
    · exact outerPay_block_018 ⟨i%256,hj⟩
    · exact outerPay_block_019 ⟨i%256,hj⟩
    · exact outerPay_block_020 ⟨i%256,hj⟩
    · exact outerPay_block_021 ⟨i%256,hj⟩
    · exact outerPay_block_022 ⟨i%256,hj⟩
    · exact outerPay_block_023 ⟨i%256,hj⟩
    · exact outerPay_block_024 ⟨i%256,hj⟩
    · exact outerPay_block_025 ⟨i%256,hj⟩
    · exact outerPay_block_026 ⟨i%256,hj⟩
    · exact outerPay_block_027 ⟨i%256,hj⟩
    · exact outerPay_block_028 ⟨i%256,hj⟩
    · exact outerPay_block_029 ⟨i%256,hj⟩
    · exact outerPay_block_030 ⟨i%256,hj⟩
    · exact outerPay_block_031 ⟨i%256,hj⟩
    · exact outerPay_block_032 ⟨i%256,hj⟩
    · exact outerPay_block_033 ⟨i%256,hj⟩
    · exact outerPay_block_034 ⟨i%256,hj⟩
    · exact outerPay_block_035 ⟨i%256,hj⟩
    · exact outerPay_block_036 ⟨i%256,hj⟩
    · exact outerPay_block_037 ⟨i%256,hj⟩
    · exact outerPay_block_038 ⟨i%256,hj⟩
    · exact outerPay_block_039 ⟨i%256,hj⟩
    · exact outerPay_block_040 ⟨i%256,hj⟩
    · exact outerPay_block_041 ⟨i%256,hj⟩
  have he : 256*(i/256)+i%256=i := by omega
  have h := hh ⟨i/256,hb⟩ (by change 256*(i/256)+i%256 < 10540; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_outerPay
