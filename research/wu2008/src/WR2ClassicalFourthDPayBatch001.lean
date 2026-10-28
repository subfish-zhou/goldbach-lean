import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativeDivision
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_008 (j : Fin 256) (hj : 256*8+j.val < 2540) :
    DPay (256*8+j.val) := by
  by_cases hb : (256*8+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*8+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*8+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*8+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*8+j.val = 256*8+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*8+4*k.val+3 < 2540 → DPay (256*8+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*8+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_009 (j : Fin 256) (hj : 256*9+j.val < 2540) :
    DPay (256*9+j.val) := by
  by_cases hb : (256*9+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*9+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*9+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*9+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*9+j.val = 256*9+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*9+4*k.val+3 < 2540 → DPay (256*9+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*9+4*(j.val/4)+3 < 2540; omega)

end WuPaper.ClassicalFourthConditions
