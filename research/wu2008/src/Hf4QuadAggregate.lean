import Hf4QuadPanel0
import Hf4QuadBatch0
import Hf4QuadBatch1
import Hf4QuadBatch2
import Hf4QuadBatch3
import Hf4QuadBatch4
import Hf4QuadBatch5
import Hf4QuadBatch6
import Hf4QuadBatch7
import Hf4QuadBatch8
import Hf4QuadBatch9
import Hf4QuadBatch10
import Hf4QuadBatch11
import Hf4QuadBatch12

noncomputable section
namespace Hf4Quad
open SigmaActualBlockSeparable

theorem cell0_split : endpointCellMass 1 (11/5) = endpointCellMass 1 (21/20) + endpointCellMass (21/20) (11/10) + endpointCellMass (11/10) (23/20) + endpointCellMass (23/20) (6/5) + endpointCellMass (6/5) (5/4) + endpointCellMass (5/4) (13/10) + endpointCellMass (13/10) (27/20) + endpointCellMass (27/20) (7/5) + endpointCellMass (7/5) (29/20) + endpointCellMass (29/20) (3/2) + endpointCellMass (3/2) (31/20) + endpointCellMass (31/20) (8/5) + endpointCellMass (8/5) (33/20) + endpointCellMass (33/20) (17/10) + endpointCellMass (17/10) (7/4) + endpointCellMass (7/4) (9/5) + endpointCellMass (9/5) (37/20) + endpointCellMass (37/20) (19/10) + endpointCellMass (19/10) (39/20) + endpointCellMass (39/20) 2 + endpointCellMass 2 (41/20) + endpointCellMass (41/20) (21/10) + endpointCellMass (21/10) (43/20) + endpointCellMass (43/20) (11/5) := by
  unfold endpointCellMass
  ring

theorem cell0_bounds : ((111258826147199/6000000000000000):ℝ) ≤ endpointCellMass 1 (11/5) ∧
    endpointCellMass 1 (11/5) ≤ (111309501265979/6000000000000000) := by
  rw [cell0_split]
  constructor
  · have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add Panel0.mass_bounds.1 Panel1.mass_bounds.1) Panel2.mass_bounds.1) Panel3.mass_bounds.1) Panel4.mass_bounds.1) Panel5.mass_bounds.1) Panel6.mass_bounds.1) Panel7.mass_bounds.1) Panel8.mass_bounds.1) Panel9.mass_bounds.1) Panel10.mass_bounds.1) Panel11.mass_bounds.1) Panel12.mass_bounds.1) Panel13.mass_bounds.1) Panel14.mass_bounds.1) Panel15.mass_bounds.1) Panel16.mass_bounds.1) Panel17.mass_bounds.1) Panel18.mass_bounds.1) Panel19.mass_bounds.1) Panel20.mass_bounds.1) Panel21.mass_bounds.1) Panel22.mass_bounds.1) Panel23.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add Panel0.mass_bounds.2 Panel1.mass_bounds.2) Panel2.mass_bounds.2) Panel3.mass_bounds.2) Panel4.mass_bounds.2) Panel5.mass_bounds.2) Panel6.mass_bounds.2) Panel7.mass_bounds.2) Panel8.mass_bounds.2) Panel9.mass_bounds.2) Panel10.mass_bounds.2) Panel11.mass_bounds.2) Panel12.mass_bounds.2) Panel13.mass_bounds.2) Panel14.mass_bounds.2) Panel15.mass_bounds.2) Panel16.mass_bounds.2) Panel17.mass_bounds.2) Panel18.mass_bounds.2) Panel19.mass_bounds.2) Panel20.mass_bounds.2) Panel21.mass_bounds.2) Panel22.mass_bounds.2) Panel23.mass_bounds.2)
    norm_num at h
    exact h

theorem cell1_split : endpointCellMass (11/5) (23/10) = endpointCellMass (11/5) (9/4) + endpointCellMass (9/4) (23/10) := by
  unfold endpointCellMass
  ring

theorem cell1_bounds : ((11015108859877/3000000000000000):ℝ) ≤ endpointCellMass (11/5) (23/10) ∧
    endpointCellMass (11/5) (23/10) ≤ (11015736059707/3000000000000000) := by
  rw [cell1_split]
  constructor
  · have h := (add_le_add Panel24.mass_bounds.1 Panel25.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel24.mass_bounds.2 Panel25.mass_bounds.2)
    norm_num at h
    exact h

theorem cell2_split : endpointCellMass (23/10) (12/5) = endpointCellMass (23/10) (47/20) + endpointCellMass (47/20) (12/5) := by
  unfold endpointCellMass
  ring

theorem cell2_bounds : ((795917363183/200000000000000):ℝ) ≤ endpointCellMass (23/10) (12/5) ∧
    endpointCellMass (23/10) (12/5) ≤ (994942098509/250000000000000) := by
  rw [cell2_split]
  constructor
  · have h := (add_le_add Panel26.mass_bounds.1 Panel27.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel26.mass_bounds.2 Panel27.mass_bounds.2)
    norm_num at h
    exact h

theorem cell3_split : endpointCellMass (12/5) (5/2) = endpointCellMass (12/5) (49/20) + endpointCellMass (49/20) (5/2) := by
  unfold endpointCellMass
  ring

theorem cell3_bounds : ((400954892897/93750000000000):ℝ) ≤ endpointCellMass (12/5) (5/2) ∧
    endpointCellMass (12/5) (5/2) ≤ (6415516038263/1500000000000000) := by
  rw [cell3_split]
  constructor
  · have h := (add_le_add Panel28.mass_bounds.1 Panel29.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel28.mass_bounds.2 Panel29.mass_bounds.2)
    norm_num at h
    exact h

theorem cell4_split : endpointCellMass (5/2) (13/5) = endpointCellMass (5/2) (51/20) + endpointCellMass (51/20) (13/5) := by
  unfold endpointCellMass
  ring

theorem cell4_bounds : ((27380225768713/6000000000000000):ℝ) ≤ endpointCellMass (5/2) (13/5) ∧
    endpointCellMass (5/2) (13/5) ≤ (27381059240143/6000000000000000) := by
  rw [cell4_split]
  constructor
  · have h := (add_le_add Panel30.mass_bounds.1 Panel31.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel30.mass_bounds.2 Panel31.mass_bounds.2)
    norm_num at h
    exact h

theorem cell5_split : endpointCellMass (13/5) (27/10) = endpointCellMass (13/5) (53/20) + endpointCellMass (53/20) (27/10) := by
  unfold endpointCellMass
  ring

theorem cell5_bounds : ((75612009467/15625000000000):ℝ) ≤ endpointCellMass (13/5) (27/10) ∧
    endpointCellMass (13/5) (27/10) ≤ (96785817797/20000000000000) := by
  rw [cell5_split]
  constructor
  · have h := (add_le_add Panel32.mass_bounds.1 Panel33.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel32.mass_bounds.2 Panel33.mass_bounds.2)
    norm_num at h
    exact h

theorem cell6_split : endpointCellMass (27/10) (14/5) = endpointCellMass (27/10) (11/4) + endpointCellMass (11/4) (14/5) := by
  unfold endpointCellMass
  ring

theorem cell6_bounds : ((10208761954023/2000000000000000):ℝ) ≤ endpointCellMass (27/10) (14/5) ∧
    endpointCellMass (27/10) (14/5) ≤ (2041795637723/400000000000000) := by
  rw [cell6_split]
  constructor
  · have h := (add_le_add Panel34.mass_bounds.1 Panel35.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel34.mass_bounds.2 Panel35.mass_bounds.2)
    norm_num at h
    exact h

theorem cell7_split : endpointCellMass (14/5) (29/10) = endpointCellMass (14/5) (57/20) + endpointCellMass (57/20) (29/10) := by
  unfold endpointCellMass
  ring

theorem cell7_bounds : ((267961103141/50000000000000):ℝ) ≤ endpointCellMass (14/5) (29/10) ∧
    endpointCellMass (14/5) (29/10) ≤ (5359317893973/1000000000000000) := by
  rw [cell7_split]
  constructor
  · have h := (add_le_add Panel36.mass_bounds.1 Panel37.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel36.mass_bounds.2 Panel37.mass_bounds.2)
    norm_num at h
    exact h

theorem cell8_split : endpointCellMass (29/10) 3 = endpointCellMass (29/10) (59/20) + endpointCellMass (59/20) 3 := by
  unfold endpointCellMass
  ring

theorem cell8_bounds : ((700494974059/125000000000000):ℝ) ≤ endpointCellMass (29/10) 3 ∧
    endpointCellMass (29/10) 3 ≤ (5604045131777/1000000000000000) := by
  rw [cell8_split]
  constructor
  · have h := (add_le_add Panel38.mass_bounds.1 Panel39.mass_bounds.1)
    norm_num at h
    exact h
  · have h := (add_le_add Panel38.mass_bounds.2 Panel39.mass_bounds.2)
    norm_num at h
    exact h

theorem original_Q_expansion : endpointNumerator NineFeedbackStrength.originalH =
    (223939/10000000) * endpointCellMass 1 (11/5) + (54299/2500000) * endpointCellMass (11/5) (23/10) + (50719/2500000) * endpointCellMass (23/10) (12/5) + (181433/10000000) * endpointCellMass (12/5) (5/2) + (39661/2500000) * endpointCellMass (5/2) (13/5) + (129923/10000000) * endpointCellMass (13/5) (27/10) + (50343/5000000) * endpointCellMass (27/10) (14/5) + (39081/5000000) * endpointCellMass (14/5) (29/10) + (72943/10000000) * endpointCellMass (29/10) 3 := by
  norm_num [endpointNumerator, Fin.sum_univ_succ, NineFeedbackStrength.originalH,
    NodeExtension.upperLeft, NodeExtension.upperNode]
  ring

theorem original_Q_bounds : ((11073123920579352283/12000000000000000000000):ℝ) ≤ endpointNumerator NineFeedbackStrength.originalH ∧
    endpointNumerator NineFeedbackStrength.originalH ≤ (55378008917319052241/60000000000000000000000) := by
  rw [original_Q_expansion]
  constructor
  · have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left cell0_bounds.1 (by norm_num : (0:ℝ) ≤ (223939/10000000))) (mul_le_mul_of_nonneg_left cell1_bounds.1 (by norm_num : (0:ℝ) ≤ (54299/2500000)))) (mul_le_mul_of_nonneg_left cell2_bounds.1 (by norm_num : (0:ℝ) ≤ (50719/2500000)))) (mul_le_mul_of_nonneg_left cell3_bounds.1 (by norm_num : (0:ℝ) ≤ (181433/10000000)))) (mul_le_mul_of_nonneg_left cell4_bounds.1 (by norm_num : (0:ℝ) ≤ (39661/2500000)))) (mul_le_mul_of_nonneg_left cell5_bounds.1 (by norm_num : (0:ℝ) ≤ (129923/10000000)))) (mul_le_mul_of_nonneg_left cell6_bounds.1 (by norm_num : (0:ℝ) ≤ (50343/5000000)))) (mul_le_mul_of_nonneg_left cell7_bounds.1 (by norm_num : (0:ℝ) ≤ (39081/5000000)))) (mul_le_mul_of_nonneg_left cell8_bounds.1 (by norm_num : (0:ℝ) ≤ (72943/10000000))))
    norm_num at h
    exact h
  · have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left cell0_bounds.2 (by norm_num : (0:ℝ) ≤ (223939/10000000))) (mul_le_mul_of_nonneg_left cell1_bounds.2 (by norm_num : (0:ℝ) ≤ (54299/2500000)))) (mul_le_mul_of_nonneg_left cell2_bounds.2 (by norm_num : (0:ℝ) ≤ (50719/2500000)))) (mul_le_mul_of_nonneg_left cell3_bounds.2 (by norm_num : (0:ℝ) ≤ (181433/10000000)))) (mul_le_mul_of_nonneg_left cell4_bounds.2 (by norm_num : (0:ℝ) ≤ (39661/2500000)))) (mul_le_mul_of_nonneg_left cell5_bounds.2 (by norm_num : (0:ℝ) ≤ (129923/10000000)))) (mul_le_mul_of_nonneg_left cell6_bounds.2 (by norm_num : (0:ℝ) ≤ (50343/5000000)))) (mul_le_mul_of_nonneg_left cell7_bounds.2 (by norm_num : (0:ℝ) ≤ (39081/5000000)))) (mul_le_mul_of_nonneg_left cell8_bounds.2 (by norm_num : (0:ℝ) ≤ (72943/10000000))))
    norm_num at h
    exact h

theorem original_Q_width : ((55378008917319052241/60000000000000000000000):ℝ) - (11073123920579352283/12000000000000000000000) = (2064885737048471/10000000000000000000000) := by norm_num

theorem original_Q_width_lt : ((2064885737048471/10000000000000000000000):ℝ) < 1/1000000 := by norm_num

theorem original_Q_below_parent_threshold : endpointNumerator NineFeedbackStrength.originalH < (48761/50000000:ℝ) :=
  lt_of_le_of_lt original_Q_bounds.2 (by norm_num)

#print axioms original_Q_bounds
#print axioms original_Q_width
#print axioms original_Q_below_parent_threshold
end Hf4Quad
