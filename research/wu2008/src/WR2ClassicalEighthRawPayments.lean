import WR2ClassicalEighthRawSums
import WR2ClassicalEighthQuadrature
noncomputable section
namespace WuPaper.ClassicalEighth
open Finset

theorem numerator_sum : (∑ i ∈ range 2048, numerator i) = 5258450040652036 := by
  rw [show 2048=32*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 32, paymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [raw_sum_block_000, raw_sum_block_001, raw_sum_block_002, raw_sum_block_003, raw_sum_block_004, raw_sum_block_005, raw_sum_block_006, raw_sum_block_007, raw_sum_block_008, raw_sum_block_009, raw_sum_block_010, raw_sum_block_011, raw_sum_block_012, raw_sum_block_013, raw_sum_block_014, raw_sum_block_015, raw_sum_block_016, raw_sum_block_017, raw_sum_block_018, raw_sum_block_019, raw_sum_block_020, raw_sum_block_021, raw_sum_block_022, raw_sum_block_023, raw_sum_block_024, raw_sum_block_025, raw_sum_block_026, raw_sum_block_027, raw_sum_block_028, raw_sum_block_029, raw_sum_block_030, raw_sum_block_031]
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.numerator_sum
