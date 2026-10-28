import WR2ClassicalEighthCorrectionTableCheck
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem conditions_000 : ∀ j : Fin 16, TableCheck.condition (16*0+j.val) := by
  decide +kernel

theorem grid_block_000 (j : Fin 16) : step*payment (16*0+j.val) ≤ cellPayment (point (16*0+j.val)) (point ((16*0+j.val)+1)) :=
  TableCheck.condition_sound (conditions_000 j)

end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_000
