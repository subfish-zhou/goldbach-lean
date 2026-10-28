import WR2XiSixthDirectCheck
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem direct_block_02 : ∀ j : Fin 32,
    DirectCheck.condition (32*2+j.val) := by
  decide +kernel

theorem grid_block_02 (j : Fin 32) : payment (32*2+j.val) ≤ panelBound (32*2+j.val) :=
  DirectCheck.condition_sound (direct_block_02 j)

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.grid_block_02
