import WR2ClassicalSixthUpperSums
import WR2ClassicalSixthAssembly
noncomputable section
namespace WuPaper.ClassicalSixthRational
open Finset

theorem upper_sum : (∑ i ∈ range 4096, upperNumerator i) = 1025832247091325 := by
  rw [show 4096=64*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 64, upperPaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [upper_sum_block_000, upper_sum_block_001, upper_sum_block_002, upper_sum_block_003, upper_sum_block_004, upper_sum_block_005, upper_sum_block_006, upper_sum_block_007, upper_sum_block_008, upper_sum_block_009, upper_sum_block_010, upper_sum_block_011, upper_sum_block_012, upper_sum_block_013, upper_sum_block_014, upper_sum_block_015, upper_sum_block_016, upper_sum_block_017, upper_sum_block_018, upper_sum_block_019, upper_sum_block_020, upper_sum_block_021, upper_sum_block_022, upper_sum_block_023, upper_sum_block_024, upper_sum_block_025, upper_sum_block_026, upper_sum_block_027, upper_sum_block_028, upper_sum_block_029, upper_sum_block_030, upper_sum_block_031, upper_sum_block_032, upper_sum_block_033, upper_sum_block_034, upper_sum_block_035, upper_sum_block_036, upper_sum_block_037, upper_sum_block_038, upper_sum_block_039, upper_sum_block_040, upper_sum_block_041, upper_sum_block_042, upper_sum_block_043, upper_sum_block_044, upper_sum_block_045, upper_sum_block_046, upper_sum_block_047, upper_sum_block_048, upper_sum_block_049, upper_sum_block_050, upper_sum_block_051, upper_sum_block_052, upper_sum_block_053, upper_sum_block_054, upper_sum_block_055, upper_sum_block_056, upper_sum_block_057, upper_sum_block_058, upper_sum_block_059, upper_sum_block_060, upper_sum_block_061, upper_sum_block_062, upper_sum_block_063]

theorem upper_total : (1025832247091325:ℝ)/1000000000000 ≤ ∑ i ∈ range 4096, upperPayment i := by
  simp only [upperPayment,← Finset.sum_div,← Nat.cast_sum,upper_sum]
  rfl
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_total
