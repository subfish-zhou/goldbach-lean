import WR2ClassicalFifthInitialSums
import WR2ClassicalFifthAssembly
noncomputable section
namespace WuPaper.ClassicalFifthRational
open Finset

def initialPayment (i : ℕ) : ℝ := (initialNumerator i:ℝ)/1000000000000

theorem initial_sum : (∑ i ∈ range 1024, initialNumerator i) = 273358482524540 := by
  rw [show 1024=16*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 16, initialPaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [initial_sum_block_000, initial_sum_block_001, initial_sum_block_002, initial_sum_block_003, initial_sum_block_004, initial_sum_block_005, initial_sum_block_006, initial_sum_block_007, initial_sum_block_008, initial_sum_block_009, initial_sum_block_010, initial_sum_block_011, initial_sum_block_012, initial_sum_block_013, initial_sum_block_014, initial_sum_block_015]

theorem initial_total : (273358482524540:ℝ)/1000000000000 ≤ ∑ i ∈ range 1024, initialPayment i := by
  simp only [initialPayment,← Finset.sum_div,← Nat.cast_sum,initial_sum]
  rfl
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_total
