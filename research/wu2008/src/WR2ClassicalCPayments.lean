import WR2ClassicalCUniform
import WR2ClassicalCSums
noncomputable section
namespace WuPaper.ClassicalC
open Finset

theorem cPayment_sum : (∑ i ∈ range 4096, cPaymentNumerator i) = 207693136875355 := by
  rw [show 4096=64*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 64, cPaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [c_sum_block_000, c_sum_block_001, c_sum_block_002, c_sum_block_003, c_sum_block_004, c_sum_block_005, c_sum_block_006, c_sum_block_007, c_sum_block_008, c_sum_block_009, c_sum_block_010, c_sum_block_011, c_sum_block_012, c_sum_block_013, c_sum_block_014, c_sum_block_015, c_sum_block_016, c_sum_block_017, c_sum_block_018, c_sum_block_019, c_sum_block_020, c_sum_block_021, c_sum_block_022, c_sum_block_023, c_sum_block_024, c_sum_block_025, c_sum_block_026, c_sum_block_027, c_sum_block_028, c_sum_block_029, c_sum_block_030, c_sum_block_031, c_sum_block_032, c_sum_block_033, c_sum_block_034, c_sum_block_035, c_sum_block_036, c_sum_block_037, c_sum_block_038, c_sum_block_039, c_sum_block_040, c_sum_block_041, c_sum_block_042, c_sum_block_043, c_sum_block_044, c_sum_block_045, c_sum_block_046, c_sum_block_047, c_sum_block_048, c_sum_block_049, c_sum_block_050, c_sum_block_051, c_sum_block_052, c_sum_block_053, c_sum_block_054, c_sum_block_055, c_sum_block_056, c_sum_block_057, c_sum_block_058, c_sum_block_059, c_sum_block_060, c_sum_block_061, c_sum_block_062, c_sum_block_063]

theorem cPayment_total : (1336108:ℝ)/10000000 ≤
    step (1327/200) 4096*(∑ i ∈ range 4096, cPayment i)-
      (4096:ℝ)*8*(step (1327/200) 4096)^3/24 := by
  simp only [cPayment,← Finset.sum_div,← Nat.cast_sum,cPayment_sum]
  norm_num [step]

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.cPayment_total
