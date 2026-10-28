import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativePayment
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_032 (j : Fin 256) (hj : 256*32+j.val < 10540) :
    BPay (256*32+j.val) := by
  by_cases hb : (256*32+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*32+j.val = 256*32+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*32+4*k.val+3 < 10540 → BPay (256*32+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*32+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_033 (j : Fin 256) (hj : 256*33+j.val < 10540) :
    BPay (256*33+j.val) := by
  by_cases hb : (256*33+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*33+j.val = 256*33+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*33+4*k.val+3 < 10540 → BPay (256*33+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*33+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_034 (j : Fin 256) (hj : 256*34+j.val < 10540) :
    BPay (256*34+j.val) := by
  by_cases hb : (256*34+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*34+j.val = 256*34+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*34+4*k.val+3 < 10540 → BPay (256*34+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*34+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_035 (j : Fin 256) (hj : 256*35+j.val < 10540) :
    BPay (256*35+j.val) := by
  by_cases hb : (256*35+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*35+j.val = 256*35+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*35+4*k.val+3 < 10540 → BPay (256*35+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*35+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_036 (j : Fin 256) (hj : 256*36+j.val < 10540) :
    BPay (256*36+j.val) := by
  by_cases hb : (256*36+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*36+j.val = 256*36+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*36+4*k.val+3 < 10540 → BPay (256*36+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*36+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_037 (j : Fin 256) (hj : 256*37+j.val < 10540) :
    BPay (256*37+j.val) := by
  by_cases hb : (256*37+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*37+j.val = 256*37+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*37+4*k.val+3 < 10540 → BPay (256*37+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*37+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_038 (j : Fin 256) (hj : 256*38+j.val < 10540) :
    BPay (256*38+j.val) := by
  by_cases hb : (256*38+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*38+j.val = 256*38+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*38+4*k.val+3 < 10540 → BPay (256*38+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*38+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_039 (j : Fin 256) (hj : 256*39+j.val < 10540) :
    BPay (256*39+j.val) := by
  by_cases hb : (256*39+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*39+j.val = 256*39+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*39+4*k.val+3 < 10540 → BPay (256*39+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*39+4*(j.val/4)+3 < 10540; omega)

end WuPaper.ClassicalFourthConditions
