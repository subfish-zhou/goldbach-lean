import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativePayment
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_016 (j : Fin 256) (hj : 256*16+j.val < 10540) :
    OuterPay (256*16+j.val) := by
  by_cases hb : (256*16+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*16+j.val = 256*16+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*16+4*k.val+3 < 10540 → OuterPay (256*16+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*16+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_017 (j : Fin 256) (hj : 256*17+j.val < 10540) :
    OuterPay (256*17+j.val) := by
  by_cases hb : (256*17+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*17+j.val = 256*17+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*17+4*k.val+3 < 10540 → OuterPay (256*17+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*17+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_018 (j : Fin 256) (hj : 256*18+j.val < 10540) :
    OuterPay (256*18+j.val) := by
  by_cases hb : (256*18+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*18+j.val = 256*18+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*18+4*k.val+3 < 10540 → OuterPay (256*18+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*18+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_019 (j : Fin 256) (hj : 256*19+j.val < 10540) :
    OuterPay (256*19+j.val) := by
  by_cases hb : (256*19+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*19+j.val = 256*19+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*19+4*k.val+3 < 10540 → OuterPay (256*19+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*19+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_020 (j : Fin 256) (hj : 256*20+j.val < 10540) :
    OuterPay (256*20+j.val) := by
  by_cases hb : (256*20+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*20+j.val = 256*20+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*20+4*k.val+3 < 10540 → OuterPay (256*20+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*20+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_021 (j : Fin 256) (hj : 256*21+j.val < 10540) :
    OuterPay (256*21+j.val) := by
  by_cases hb : (256*21+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*21+j.val = 256*21+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*21+4*k.val+3 < 10540 → OuterPay (256*21+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*21+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_022 (j : Fin 256) (hj : 256*22+j.val < 10540) :
    OuterPay (256*22+j.val) := by
  by_cases hb : (256*22+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*22+j.val = 256*22+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*22+4*k.val+3 < 10540 → OuterPay (256*22+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*22+4*(j.val/4)+3 < 10540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_023 (j : Fin 256) (hj : 256*23+j.val < 10540) :
    OuterPay (256*23+j.val) := by
  by_cases hb : (256*23+j.val)%4 ≠ 3
  · simpa only [OuterPay, ClassicalFourthData.outer] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.outerq 56
        ClassicalFourthData.outerAnchor hj hb
  · have hk : j.val/4 < 64 := by omega
    have he : 256*23+j.val = 256*23+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold OuterPay; decide +kernel :
      ∀ k : Fin 64, 256*23+4*k.val+3 < 10540 → OuterPay (256*23+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*23+4*(j.val/4)+3 < 10540; omega)

end WuPaper.ClassicalFourthConditions
