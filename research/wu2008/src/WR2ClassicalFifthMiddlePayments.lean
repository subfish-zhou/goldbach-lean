import WR2ClassicalFifthMiddleSums
import WR2ClassicalFifthAssembly
noncomputable section
namespace WuPaper.ClassicalFifthRational
open Finset

def middlePayment (i : ℕ) : ℝ := (middleNumerator i:ℝ)/1000000000000

theorem middle_sum : (∑ i ∈ range 1024, middleNumerator i) = 661191362320992 := by
  rw [show 1024=16*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 16, middlePaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [middle_sum_block_000, middle_sum_block_001, middle_sum_block_002, middle_sum_block_003, middle_sum_block_004, middle_sum_block_005, middle_sum_block_006, middle_sum_block_007, middle_sum_block_008, middle_sum_block_009, middle_sum_block_010, middle_sum_block_011, middle_sum_block_012, middle_sum_block_013, middle_sum_block_014, middle_sum_block_015]

theorem middle_total : (661191362320992:ℝ)/1000000000000 ≤ ∑ i ∈ range 1024, middlePayment i := by
  simp only [middlePayment,← Finset.sum_div,← Nat.cast_sum,middle_sum]
  rfl
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_total
