import WR2ClassicalFifthTerminalSums
import WR2ClassicalFifthAssembly
noncomputable section
namespace WuPaper.ClassicalFifthRational
open Finset

def terminalPayment (i : ℕ) : ℝ := (terminalNumerator i:ℝ)/1000000000000

theorem terminal_sum : (∑ i ∈ range 1024, terminalNumerator i) = 405237426677551 := by
  rw [show 1024=16*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 16, terminalPaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [terminal_sum_block_000, terminal_sum_block_001, terminal_sum_block_002, terminal_sum_block_003, terminal_sum_block_004, terminal_sum_block_005, terminal_sum_block_006, terminal_sum_block_007, terminal_sum_block_008, terminal_sum_block_009, terminal_sum_block_010, terminal_sum_block_011, terminal_sum_block_012, terminal_sum_block_013, terminal_sum_block_014, terminal_sum_block_015]

theorem terminal_total : (405237426677551:ℝ)/1000000000000 ≤ ∑ i ∈ range 1024, terminalPayment i := by
  simp only [terminalPayment,← Finset.sum_div,← Nat.cast_sum,terminal_sum]
  rfl
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_total
