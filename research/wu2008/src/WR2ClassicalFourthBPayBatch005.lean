import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativePayment
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_040 (j : Fin 256) (hj : 256*40+j.val < 10540) :
    BPay (256*40+j.val) := by
  by_cases hb : (256*40+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*40+j.val = 256*40+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*40+4*k.val+3 < 10540 → BPay (256*40+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*40+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_041 (j : Fin 256) (hj : 256*41+j.val < 10540) :
    BPay (256*41+j.val) := by
  by_cases hb : (256*41+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*41+j.val = 256*41+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*41+4*k.val+3 < 10540 → BPay (256*41+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*41+4*(j.val/4)+3 < 10540; omega)

end WuPaper.ClassicalFourthConditions
