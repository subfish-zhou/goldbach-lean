import WR2ClassicalSixthLowerSums
import WR2ClassicalSixthAssembly
noncomputable section
namespace WuPaper.ClassicalSixthRational
open Finset

theorem lower_sum : (∑ i ∈ range 4096, lowerNumerator i) = 939922834048256 := by
  rw [show 4096=64*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 64, lowerPaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [lower_sum_block_000, lower_sum_block_001, lower_sum_block_002, lower_sum_block_003, lower_sum_block_004, lower_sum_block_005, lower_sum_block_006, lower_sum_block_007, lower_sum_block_008, lower_sum_block_009, lower_sum_block_010, lower_sum_block_011, lower_sum_block_012, lower_sum_block_013, lower_sum_block_014, lower_sum_block_015, lower_sum_block_016, lower_sum_block_017, lower_sum_block_018, lower_sum_block_019, lower_sum_block_020, lower_sum_block_021, lower_sum_block_022, lower_sum_block_023, lower_sum_block_024, lower_sum_block_025, lower_sum_block_026, lower_sum_block_027, lower_sum_block_028, lower_sum_block_029, lower_sum_block_030, lower_sum_block_031, lower_sum_block_032, lower_sum_block_033, lower_sum_block_034, lower_sum_block_035, lower_sum_block_036, lower_sum_block_037, lower_sum_block_038, lower_sum_block_039, lower_sum_block_040, lower_sum_block_041, lower_sum_block_042, lower_sum_block_043, lower_sum_block_044, lower_sum_block_045, lower_sum_block_046, lower_sum_block_047, lower_sum_block_048, lower_sum_block_049, lower_sum_block_050, lower_sum_block_051, lower_sum_block_052, lower_sum_block_053, lower_sum_block_054, lower_sum_block_055, lower_sum_block_056, lower_sum_block_057, lower_sum_block_058, lower_sum_block_059, lower_sum_block_060, lower_sum_block_061, lower_sum_block_062, lower_sum_block_063]

theorem lower_total : (939922834048256:ℝ)/1000000000000 ≤ ∑ i ∈ range 4096, lowerPayment i := by
  simp only [lowerPayment,← Finset.sum_div,← Nat.cast_sum,lower_sum]
  rfl
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_total
