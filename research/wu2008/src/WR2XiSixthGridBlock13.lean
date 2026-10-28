import WR2XiSixthDirectCheck
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem direct_block_13 : ∀ j : Fin 32,
    DirectCheck.condition (32*13+j.val) := by
  decide +kernel

theorem grid_block_13 (j : Fin 32) : payment (32*13+j.val) ≤ panelBound (32*13+j.val) :=
  DirectCheck.condition_sound (direct_block_13 j)

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_13
