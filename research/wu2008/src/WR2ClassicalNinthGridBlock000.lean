import WR2ClassicalNinthTableCheck
namespace WuPaper.ClassicalNinth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem grid_block_000 (j : Fin 64) : upperValue ((point (64*0+j.val)+point ((64*0+j.val)+1))/2) ≤ payment (64*0+j.val) := by
  apply ClassicalNinthTableCheck.condition_sound
  exact (by unfold ClassicalNinthTableCheck.condition; decide +kernel :
    ∀ j : Fin 64, ClassicalNinthTableCheck.condition (64*0+j.val)) j
end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.grid_block_000
