import Mathlib.Tactic.FinCases
import WR2ClassicalFourthDPayBatch000
import WR2ClassicalFourthDPayBatch001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_DPay (i : ℕ) (hi : i < 2540) : DPay (i) := by
  have hj : i%256 < 256 := Nat.mod_lt _ (by norm_num)
  have hb : i/256 < 10 := by omega
  have hh (b : Fin 10) : 256*b.val+i%256 < 2540 → DPay (256*b.val+i%256) := by
    fin_cases b
    · exact DPay_block_000 ⟨i%256,hj⟩
    · exact DPay_block_001 ⟨i%256,hj⟩
    · exact DPay_block_002 ⟨i%256,hj⟩
    · exact DPay_block_003 ⟨i%256,hj⟩
    · exact DPay_block_004 ⟨i%256,hj⟩
    · exact DPay_block_005 ⟨i%256,hj⟩
    · exact DPay_block_006 ⟨i%256,hj⟩
    · exact DPay_block_007 ⟨i%256,hj⟩
    · exact DPay_block_008 ⟨i%256,hj⟩
    · exact DPay_block_009 ⟨i%256,hj⟩
  have he : 256*(i/256)+i%256=i := by omega
  have h := hh ⟨i/256,hb⟩ (by change 256*(i/256)+i%256 < 2540; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_DPay
