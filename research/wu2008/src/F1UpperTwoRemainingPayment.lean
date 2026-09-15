import F1ActualMomentPayment

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment
namespace F1RemainingRecovery

def upperTwoA : ℝ := (1287/3178267:ℝ)
def upperTwoPayment : ℝ := (1287/22247869:ℝ)
def upperTwoPrimitive (t : ℝ) : ℝ :=
  (160/1:ℝ)*(t-1)^7/7+
  (640/1:ℝ)*(t-1)^8/8+
  (1040/1:ℝ)*(t-1)^9/9+
  (880/1:ℝ)*(t-1)^10/10+
  (410/1:ℝ)*(t-1)^11/11+
  (100/1:ℝ)*(t-1)^12/12+
  (10/1:ℝ)*(t-1)^13/13

theorem upperTwoPrimitive_deriv (t : ℝ) : HasDerivAt upperTwoPrimitive
    ((t-1)^6*(10*t^2*(t+1)^4)) t := by
  have hd := (hasDerivAt_id t).sub_const 1
  have h0 := ((hd.pow 7).const_mul (160/1:ℝ)).div_const 7
  have h1 := ((hd.pow 8).const_mul (640/1:ℝ)).div_const 8
  have h2 := ((hd.pow 9).const_mul (1040/1:ℝ)).div_const 9
  have h3 := ((hd.pow 10).const_mul (880/1:ℝ)).div_const 10
  have h4 := ((hd.pow 11).const_mul (410/1:ℝ)).div_const 11
  have h5 := ((hd.pow 12).const_mul (100/1:ℝ)).div_const 12
  have h6 := ((hd.pow 13).const_mul (10/1:ℝ)).div_const 13
  have h := ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6)
  convert h using 1 <;> first | rfl | (dsimp [upperTwoPrimitive]; ring)

theorem upperTwo_comparison_deriv {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => JointLogTotalComparison.V t-log t-
      (2*upperTwoA*(t-1)^7/7-upperTwoA^2*upperTwoPrimitive t))
      ((t-1)^6/(10*t^2*(t+1)^4)-
        (2*upperTwoA*(t-1)^6-upperTwoA^2*((t-1)^6*(10*t^2*(t+1)^4)))) t := by
  have hd := (hasDerivAt_id t).sub_const 1
  have h := (upper_gap_deriv ht).sub
    ((((hd.pow 7).const_mul (2*upperTwoA)).div_const 7).sub
      ((upperTwoPrimitive_deriv t).const_mul (upperTwoA^2)))
  convert h using 1 <;> first | rfl | (dsimp; ring)

/-- Payment specifically from the remaining original log(2) error. -/
theorem upperTwoPayment_le : upperTwoPayment ≤ JointLogTotalComparison.V 2-log 2 := by
  let f : ℝ → ℝ := fun t => JointLogTotalComparison.V t-log t-
    (2*upperTwoA*(t-1)^7/7-upperTwoA^2*upperTwoPrimitive t)
  have hd (t : ℝ) (ht : t ∈ Icc 1 2) := upperTwo_comparison_deriv ht.1
  have hm : MonotoneOn f (Icc 1 2) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 2)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have htI : t ∈ Icc 1 2 := interior_subset ht
    have ht0 : 0 < t := by linarith [htI.1]
    have hq : 0 < 10*t^2*(t+1)^4 := by positivity
    have h := weighted_square_payment (w := (t-1)^6) (by positivity) hq upperTwoA
    rw [mul_div_assoc] at h
    linarith only [h]
  have h := hm (by norm_num : (1:ℝ) ∈ Icc 1 2)
    (by norm_num : (2:ℝ) ∈ Icc 1 2) (by norm_num)
  have hbase : f 1 = 0 := by
    norm_num [f,upperTwoPrimitive,JointLogTotalComparison.V,upperLog,lowerLog]
  have hend : f 2 = JointLogTotalComparison.V 2-log 2-upperTwoPayment := by
    dsimp [f]
    congr 1
    norm_num [upperTwoA,upperTwoPayment,upperTwoPrimitive]
  rw [hbase,hend] at h
  exact sub_nonneg.mp h

theorem upperTwoPayment_improves : upperGapPayment 2 < upperTwoPayment := by
  norm_num [upperGapPayment,upperTwoPayment]

end F1RemainingRecovery
