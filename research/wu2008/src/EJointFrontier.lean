import EJointAssembly
noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery F1SecondLogRecovery
namespace EJoint
theorem W_fixed_exact : W (1327/200) = (11386442747536701:ℝ)/448000000000000000 := by
  rw [W_exact]
  norm_num [A4]
theorem Q_fixed_exact : Q (1327/200) = (2048187671058796237750102568259702849087:ℝ)/13120307200000000000000000000000000000 := by
  rw [Q_exact]
  norm_num [B4]
theorem fixedA_fixed_exact : fixedA = (3364450918400000000000000:ℝ)/20664737271858587902354448747 := by
  unfold fixedA
  rw [W_fixed_exact,Q_fixed_exact]
  norm_num
theorem payment_fixed_exact : payment = (2992900606192099454465328:ℝ)/723265804515050576582405706145 := by
  unfold payment
  rw [W_fixed_exact,Q_fixed_exact]
  norm_num
theorem fixedQ_pos : 0 < Q (1327/200) := by rw [Q_fixed_exact]; norm_num

theorem remainingDebit_pos : 0 < remainingDebit := by
  unfold remainingDebit
  rw [payment_fixed_exact]
  unfold F1SecondLogRecovery.remainingDebit
  rw [show F1KernelUpperAssembly.debit = rationalPublicationDebit-
    F1KernelUpperAssembly.logPayment-momentPayment by rfl]
  rw [momentPayment_exact,unpaidFactorPayment_exact]
  unfold combinedSquarePayment
  rw [squarePayment_exact]
  norm_num [F1KernelUpperAssembly.logPayment,fourLowerRecoveryPayment,
    upperTwoPayment,upperGapPayment,lowerGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC,residueD,rationalPublicationDebit,secondFactorRatio,
    F1LowerResidual.logPaymentExtra,F1LowerResidual.payment,F1LowerResidual.denom,
    secondPayment,massW,massQOne,massQTwo]

theorem coefficient_lt_original_target : coefficient < (14900897:ℝ)/1000000 := by
  have h := remainingDebit_pos
  unfold coefficient
  linarith only [h]

end EJoint
