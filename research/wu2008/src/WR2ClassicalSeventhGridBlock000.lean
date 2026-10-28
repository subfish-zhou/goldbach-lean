import WR2ClassicalSeventhTableCheck
namespace WuPaper.ClassicalSeventh
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem grid_block_000 (j : Fin 64) : upperValue ((point (64*0+j.val)+point ((64*0+j.val)+1))/2) ≤ payment (64*0+j.val) := by
  apply ClassicalSeventhTableCheck.condition_sound
  exact (by unfold ClassicalSeventhTableCheck.condition; decide +kernel :
    ∀ j : Fin 64, ClassicalSeventhTableCheck.condition (64*0+j.val)) j
end WuPaper.ClassicalSeventh
