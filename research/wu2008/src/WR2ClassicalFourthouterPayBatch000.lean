import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativePayment
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_000 (j : Fin 256) (hj : 256*0+j.val < 10540) :
    OuterPay (256*0+j.val) := by
  by_cases hb : (256*0+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*0+j.val = 256*0+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*0+4*k.val+3 < 10540 → OuterPay (256*0+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*0+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_001 (j : Fin 256) (hj : 256*1+j.val < 10540) :
    OuterPay (256*1+j.val) := by
  by_cases hb : (256*1+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*1+j.val = 256*1+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*1+4*k.val+3 < 10540 → OuterPay (256*1+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*1+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_002 (j : Fin 256) (hj : 256*2+j.val < 10540) :
    OuterPay (256*2+j.val) := by
  by_cases hb : (256*2+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*2+j.val = 256*2+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*2+4*k.val+3 < 10540 → OuterPay (256*2+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*2+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_003 (j : Fin 256) (hj : 256*3+j.val < 10540) :
    OuterPay (256*3+j.val) := by
  by_cases hb : (256*3+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*3+j.val = 256*3+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*3+4*k.val+3 < 10540 → OuterPay (256*3+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*3+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_004 (j : Fin 256) (hj : 256*4+j.val < 10540) :
    OuterPay (256*4+j.val) := by
  by_cases hb : (256*4+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*4+j.val = 256*4+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*4+4*k.val+3 < 10540 → OuterPay (256*4+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*4+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_005 (j : Fin 256) (hj : 256*5+j.val < 10540) :
    OuterPay (256*5+j.val) := by
  by_cases hb : (256*5+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*5+j.val = 256*5+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*5+4*k.val+3 < 10540 → OuterPay (256*5+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*5+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_006 (j : Fin 256) (hj : 256*6+j.val < 10540) :
    OuterPay (256*6+j.val) := by
  by_cases hb : (256*6+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*6+j.val = 256*6+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*6+4*k.val+3 < 10540 → OuterPay (256*6+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*6+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_007 (j : Fin 256) (hj : 256*7+j.val < 10540) :
    OuterPay (256*7+j.val) := by
  by_cases hb : (256*7+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*7+j.val = 256*7+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*7+4*k.val+3 < 10540 → OuterPay (256*7+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*7+4*(j.val/4)+3 < 10540; omega)

end WuPaper.ClassicalFourthConditions
