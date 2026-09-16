import RemainingHfCells
import W02Transfer
import W06SigmaV2
import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FifthGainNodes

open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open WuTarget
open scoped BigOperators

def sourceVector : Fin 9 → ℝ :=
  ![18803317/1000000000,18187144/1000000000,16806736/1000000000,
    15160322/1000000000,13933425/1000000000,11221052/1000000000,
    8434404/1000000000,6314864/1000000000,5909403/1000000000]

theorem source_vector_nonnegative (k : Fin 9) : 0 ≤ sourceVector k := by
  fin_cases k <;> norm_num [sourceVector]

def tailPaid (S : ℝ) (k : Fin 9) : ℝ :=
  if W02.tailLeft S k ≤ upperNode k then
    max 0 (RemainingHf.paidCell S (W02.tailLeft S k) (upperNode k))
  else 0

theorem tail_paid_nonnegative (S : ℝ) (k : Fin 9) : 0 ≤ tailPaid S k := by
  unfold tailPaid
  split_ifs
  · exact le_max_left _ _
  · rfl

theorem tail_paid_lower {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    tailPaid S k ≤ logMoment (nodeBasis k) S := by
  have hn := W02.logMoment_basis_nonneg hS hS5 k
  rw [W02.logMoment_basis_eq hS hS5] at hn ⊢
  unfold tailPaid W02.tailIntegral at *
  split_ifs with ho
  · simp only [if_pos ho] at hn
    exact max_le hn
      (RemainingHf.paidCell_paid hS (le_max_right _ _) ho)
  · rfl

def upperPaid (i : ℕ) : ℝ :=
  if h : 2 ≤ i ∧ i ≤ 10 then sourceVector ⟨i-2,by omega⟩
  else ∑ k : Fin 9, sourceVector k *
    (W06.sigmaCoeff k * TableBounds.logLower (4/(rNode i-1))+tailPaid (rNode i) k)

theorem upper_paid_nonnegative {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    0 ≤ upperPaid i := by
  unfold upperPaid
  split_ifs with h
  · exact source_vector_nonnegative _
  · have hg := W02.extended_bounds hi hi29 h
    have hx : 1 ≤ 4/(rNode i-1) :=
      (one_le_div (by linarith : 0 < rNode i-1)).mpr (by linarith)
    have hl : 0 ≤ TableBounds.logLower (4/(rNode i-1)) := by
      unfold TableBounds.logLower
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro j _
      apply div_nonneg
      · exact pow_nonneg (div_nonneg (by linarith) (by linarith)) _
      · positivity
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (source_vector_nonnegative k)
      (add_nonneg (mul_nonneg (W06.sigmaCoeff_pos k).le hl) (tail_paid_nonnegative _ _)))

theorem upper_paid_lower {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    upperPaid i ≤ extendedNode sourceVector i := by
  by_cases h : 2 ≤ i ∧ i ≤ 10
  · simp only [upperPaid,extendedNode,dif_pos h,le_refl]
  · have hg := W02.extended_bounds hi hi29 h
    rw [upperPaid,dif_neg h,extendedNode,dif_neg h,
      eProfile_expansion _ hg.1 hg.2]
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (source_vector_nonnegative k)
    have hx : 1 ≤ 4/(rNode i-1) :=
      (one_le_div (by linarith : 0 < rNode i-1)).mpr (by linarith)
    have hl := mul_le_mul_of_nonneg_left (TableBounds.logLower_le hx)
      (W06.sigmaCoeff_pos k).le
    have hs := mul_le_mul_of_nonneg_right (W06.sigmaCoeff_le_aProfile k) (log_nonneg hx)
    have ht := tail_paid_lower hg.1 hg.2 k
    change _ ≤ aProfile (nineProfile (nodeBasis k))*log (4/(rNode i-1))+
      logMoment (nodeBasis k) (rNode i)
    linarith only [hl,hs,ht]

def lowerPaid (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (max 3 (j-9)) 29,
    upperPaid i * TableBounds.logLower (rNode i/rNode (i-1))

theorem lower_paid_lower {j : ℕ} (hj : 15 ≤ j) (hj27 : j ≤ 27) :
    lowerPaid j ≤ originalTransfer sourceVector j := by
  have he := start_log_zero (j := j) (by omega)
  change log (rNode (max 2 (j-10))/(rNode j-1)) = 0 at he
  rw [originalTransfer,he,mul_zero,zero_add]
  apply Finset.sum_le_sum
  intro i hi
  have hb := Finset.mem_Icc.mp hi
  have hi2 : 2 ≤ i := by omega
  have hx : 1 ≤ rNode i/rNode (i-1) :=
    (one_le_div (rNode_pos _)).mpr (rNode_mono (by omega))
  have hp := upper_paid_lower hi2 hb.2
  have hn := upper_paid_nonnegative hi2 hb.2
  exact (mul_le_mul_of_nonneg_left (TableBounds.logLower_le hx) hn).trans
    (mul_le_mul_of_nonneg_right hp (log_nonneg hx))

end Wu18938Campaign.M3.Confirmed.FifthGainNodes
