import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativePayment
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_024 (j : Fin 256) (hj : 256*24+j.val < 10540) :
    BPay (256*24+j.val) := by
  by_cases hb : (256*24+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*24+j.val = 256*24+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*24+4*k.val+3 < 10540 → BPay (256*24+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*24+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_025 (j : Fin 256) (hj : 256*25+j.val < 10540) :
    BPay (256*25+j.val) := by
  by_cases hb : (256*25+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*25+j.val = 256*25+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*25+4*k.val+3 < 10540 → BPay (256*25+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*25+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_026 (j : Fin 256) (hj : 256*26+j.val < 10540) :
    BPay (256*26+j.val) := by
  by_cases hb : (256*26+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*26+j.val = 256*26+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*26+4*k.val+3 < 10540 → BPay (256*26+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*26+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_027 (j : Fin 256) (hj : 256*27+j.val < 10540) :
    BPay (256*27+j.val) := by
  by_cases hb : (256*27+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*27+j.val = 256*27+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*27+4*k.val+3 < 10540 → BPay (256*27+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*27+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_028 (j : Fin 256) (hj : 256*28+j.val < 10540) :
    BPay (256*28+j.val) := by
  by_cases hb : (256*28+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*28+j.val = 256*28+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*28+4*k.val+3 < 10540 → BPay (256*28+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*28+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_029 (j : Fin 256) (hj : 256*29+j.val < 10540) :
    BPay (256*29+j.val) := by
  by_cases hb : (256*29+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*29+j.val = 256*29+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*29+4*k.val+3 < 10540 → BPay (256*29+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*29+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_030 (j : Fin 256) (hj : 256*30+j.val < 10540) :
    BPay (256*30+j.val) := by
  by_cases hb : (256*30+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*30+j.val = 256*30+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*30+4*k.val+3 < 10540 → BPay (256*30+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*30+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_031 (j : Fin 256) (hj : 256*31+j.val < 10540) :
    BPay (256*31+j.val) := by
  by_cases hb : (256*31+j.val)%4 ≠ 3
  · simpa only [BPay, ClassicalFourthData.B] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.Bq 2
        ClassicalFourthData.BAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*31+j.val = 256*31+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold BPay; decide +kernel :
      ∀ k : Fin 64, 256*31+4*k.val+3 < 10540 → BPay (256*31+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*31+4*(j.val/4)+3 < 10540; omega)

end WuPaper.ClassicalFourthConditions
