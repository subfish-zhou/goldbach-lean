import Wu18938Campaign.M3.Confirmed.FifthGainPaid

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FifthGainNodes

open Real Wu2008DoubleSieve NodeExtension WuTarget
open scoped BigOperators

def fixedNode (i : ℕ) : ℝ :=
  if h : 2 ≤ i ∧ i ≤ 10 then sourceVector ⟨i-2,by omega⟩
  else if h : 11 ≤ i ∧ i ≤ 29 then fixedUpper ⟨i-11,by omega⟩ else 0

theorem fixed_node_lower {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    fixedNode i ≤ upperPaid i := by
  by_cases hd : 2 ≤ i ∧ i ≤ 10
  · simp only [fixedNode,upperPaid,dif_pos hd,le_refl]
  · have he : 11 ≤ i ∧ i ≤ 29 := by omega
    rw [fixedNode,dif_neg hd,dif_pos he]
    convert fixed_upper_paid ⟨i-11,by omega⟩ using 1
    congr 1
    omega

def fixedTransfer (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (max 3 (j-9)) 29,
    fixedNode i * TableBounds.logLower (rNode i/rNode (i-1))

theorem log_weight_nonnegative {i : ℕ} (hi : 2 ≤ i) :
    0 ≤ TableBounds.logLower (rNode i/rNode (i-1)) := by
  have hx : 1 ≤ rNode i/rNode (i-1) :=
    (one_le_div (rNode_pos _)).mpr (rNode_mono (by omega))
  unfold TableBounds.logLower
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  apply div_nonneg
  · exact pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  · positivity

theorem fixed_transfer_lower {j : ℕ} (hj : 15 ≤ j) (hj27 : j ≤ 27) :
    fixedTransfer j ≤ originalTransfer sourceVector j := by
  apply le_trans (b := lowerPaid j) _ (lower_paid_lower hj hj27)
  apply Finset.sum_le_sum
  intro i hi
  have hb := Finset.mem_Icc.mp hi
  have hi2 : 2 ≤ i := by omega
  exact mul_le_mul_of_nonneg_right (fixed_node_lower hi2 hb.2)
    (log_weight_nonnegative hi2)

def transferFloor (k : Fin 13) : ℝ :=
  ![25486924,20022136,15787274,12719880,10503911,8500531,6802740,
    5409740,4270495,3342740,2591264,1986576,1503855] k / (10000000000:ℝ)

attribute [local simp] fixedTransfer fixedNode fixedUpper transferFloor
  sourceVector TableBounds.logLower rNode

theorem transfer_floor_0 : transferFloor 0 ≤ fixedTransfer 15 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_1 : transferFloor 1 ≤ fixedTransfer 16 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_2 : transferFloor 2 ≤ fixedTransfer 17 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_3 : transferFloor 3 ≤ fixedTransfer 18 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_4 : transferFloor 4 ≤ fixedTransfer 19 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_5 : transferFloor 5 ≤ fixedTransfer 20 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_6 : transferFloor 6 ≤ fixedTransfer 21 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_7 : transferFloor 7 ≤ fixedTransfer 22 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_8 : transferFloor 8 ≤ fixedTransfer 23 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_9 : transferFloor 9 ≤ fixedTransfer 24 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_10 : transferFloor 10 ≤ fixedTransfer 25 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_11 : transferFloor 11 ≤ fixedTransfer 26 := by norm_num [Finset.sum_Icc_succ_top]
theorem transfer_floor_12 : transferFloor 12 ≤ fixedTransfer 27 := by norm_num [Finset.sum_Icc_succ_top]

theorem transfer_floor_paid (k : Fin 13) : transferFloor k ≤ fixedTransfer (15+k) := by
  fin_cases k
  · exact transfer_floor_0
  · exact transfer_floor_1
  · exact transfer_floor_2
  · exact transfer_floor_3
  · exact transfer_floor_4
  · exact transfer_floor_5
  · exact transfer_floor_6
  · exact transfer_floor_7
  · exact transfer_floor_8
  · exact transfer_floor_9
  · exact transfer_floor_10
  · exact transfer_floor_11
  · exact transfer_floor_12

theorem transferred_lower_nodes (k : Fin 13) :
    transferFloor k ≤ originalTransfer sourceVector (15+k) :=
  (transfer_floor_paid k).trans (fixed_transfer_lower (by omega) (by omega))

end Wu18938Campaign.M3.Confirmed.FifthGainNodes
