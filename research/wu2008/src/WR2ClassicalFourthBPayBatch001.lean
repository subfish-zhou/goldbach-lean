import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativePayment
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_008 (j : Fin 256) (hj : 256*8+j.val < 10540) :
    BPay (256*8+j.val) := by
  by_cases hb : (256*8+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*8+j.val = 256*8+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*8+4*k.val+3 < 10540 → BPay (256*8+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*8+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_009 (j : Fin 256) (hj : 256*9+j.val < 10540) :
    BPay (256*9+j.val) := by
  by_cases hb : (256*9+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*9+j.val = 256*9+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*9+4*k.val+3 < 10540 → BPay (256*9+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*9+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_010 (j : Fin 256) (hj : 256*10+j.val < 10540) :
    BPay (256*10+j.val) := by
  by_cases hb : (256*10+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*10+j.val = 256*10+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*10+4*k.val+3 < 10540 → BPay (256*10+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*10+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_011 (j : Fin 256) (hj : 256*11+j.val < 10540) :
    BPay (256*11+j.val) := by
  by_cases hb : (256*11+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*11+j.val = 256*11+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*11+4*k.val+3 < 10540 → BPay (256*11+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*11+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_012 (j : Fin 256) (hj : 256*12+j.val < 10540) :
    BPay (256*12+j.val) := by
  by_cases hb : (256*12+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*12+j.val = 256*12+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*12+4*k.val+3 < 10540 → BPay (256*12+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*12+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_013 (j : Fin 256) (hj : 256*13+j.val < 10540) :
    BPay (256*13+j.val) := by
  by_cases hb : (256*13+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*13+j.val = 256*13+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*13+4*k.val+3 < 10540 → BPay (256*13+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*13+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_014 (j : Fin 256) (hj : 256*14+j.val < 10540) :
    BPay (256*14+j.val) := by
  by_cases hb : (256*14+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*14+j.val = 256*14+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*14+4*k.val+3 < 10540 → BPay (256*14+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*14+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_015 (j : Fin 256) (hj : 256*15+j.val < 10540) :
    BPay (256*15+j.val) := by
  by_cases hb : (256*15+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*15+j.val = 256*15+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*15+4*k.val+3 < 10540 → BPay (256*15+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*15+4*(j.val/4)+3 < 10540; omega)

end WuPaper.ClassicalFourthConditions
