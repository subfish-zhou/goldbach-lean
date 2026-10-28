import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativeDivision
namespace WuPaper.ClassicalFourthConditions

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_000 (j : Fin 256) (hj : 256*0+j.val < 2540) :
    DPay (256*0+j.val) := by
  by_cases hb : (256*0+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*0+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*0+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*0+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*0+j.val = 256*0+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*0+4*k.val+3 < 2540 → DPay (256*0+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*0+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_001 (j : Fin 256) (hj : 256*1+j.val < 2540) :
    DPay (256*1+j.val) := by
  by_cases hb : (256*1+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*1+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*1+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*1+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*1+j.val = 256*1+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*1+4*k.val+3 < 2540 → DPay (256*1+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*1+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_002 (j : Fin 256) (hj : 256*2+j.val < 2540) :
    DPay (256*2+j.val) := by
  by_cases hb : (256*2+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*2+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*2+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*2+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*2+j.val = 256*2+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*2+4*k.val+3 < 2540 → DPay (256*2+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*2+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_003 (j : Fin 256) (hj : 256*3+j.val < 2540) :
    DPay (256*3+j.val) := by
  by_cases hb : (256*3+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*3+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*3+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*3+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*3+j.val = 256*3+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*3+4*k.val+3 < 2540 → DPay (256*3+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*3+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_004 (j : Fin 256) (hj : 256*4+j.val < 2540) :
    DPay (256*4+j.val) := by
  by_cases hb : (256*4+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*4+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*4+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*4+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*4+j.val = 256*4+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*4+4*k.val+3 < 2540 → DPay (256*4+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*4+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_005 (j : Fin 256) (hj : 256*5+j.val < 2540) :
    DPay (256*5+j.val) := by
  by_cases hb : (256*5+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*5+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*5+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*5+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*5+j.val = 256*5+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*5+4*k.val+3 < 2540 → DPay (256*5+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*5+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_006 (j : Fin 256) (hj : 256*6+j.val < 2540) :
    DPay (256*6+j.val) := by
  by_cases hb : (256*6+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*6+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*6+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*6+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*6+j.val = 256*6+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*6+4*k.val+3 < 2540 → DPay (256*6+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*6+4*(j.val/4)+3 < 2540; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_007 (j : Fin 256) (hj : 256*7+j.val < 2540) :
    DPay (256*7+j.val) := by
  by_cases hb : (256*7+j.val)%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.C 16000 1
      ClassicalFourthData.DAnchor (i := 256*7+j.val) (by omega) hb (by omega)
    simpa only [DPay, ClassicalFourthData.D,
      if_pos (show 256*7+j.val ≤ 2540 from Nat.le_of_lt hj), if_pos (show 256*7+j.val+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < 64 := by omega
    have he : 256*7+j.val = 256*7+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold DPay; decide +kernel :
      ∀ k : Fin 64, 256*7+4*k.val+3 < 2540 → DPay (256*7+4*k.val+3))
      ⟨j.val/4,hk⟩ (by change 256*7+4*(j.val/4)+3 < 2540; omega)

end WuPaper.ClassicalFourthConditions
