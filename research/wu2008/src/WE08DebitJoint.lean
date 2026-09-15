import WE08DebitLog

noncomputable section
open Real Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison

namespace WuTarget.E08Debit

def jointConstant : ℝ :=
  W12.paymentEndpoint -
    SignedTotalCorrelation.jTwo * (V (4/3) + V (3/2)) +
    4 * (2639/1000000) + 4 * U8ActualThreshold.gainLower -
    4 * JJointPayment.paid (fun _ => 0) (fun _ => 0)

def commonCoefficient : ℝ :=
  SignedTotalCorrelation.jTwo - 4 * (23343409479070814/1325818019511839835)

def jointPacket (L H : ℝ → ℝ) : ℝ :=
  jointConstant + commonCoefficient * (H (4/3) + H (3/2)) +
    (424/15) * H (2654/2181) +
    (448/15) * H (5781/5308) -
    (8/5) * L (1800/1327) +
    (10/3) * H (1327/1200) +
    (32/15) * H (3681/2654) -
    (6/5) * L (2354/1327) +
    (25545292637193600/3273624739535407) * H (74881/66350) +
    (13984734720/2336752783) * H (240187/198481) -
    (10616/9635) * L (27551/20600) +
    (896/405) * H (1227/800)

theorem joint_collection :
    (3/5) * JJointEnvelope.upperMass +
      (2/5) * JFourRemainingMagnitude.jLowerReal = jointPacket log log := by
  have h := JJointEnvelope.gain_packet_identity
  rw [JJointPayment.collected] at h
  unfold JJointEnvelope.newJLower SignedTotalCorrelation.d2
    SignedTotalCorrelation.e2 at h
  rw [GlobalSignedActualComparison.log_two] at h
  unfold jointPacket jointConstant commonCoefficient W12.paymentEndpoint
    JJointPayment.paid
  unfold JJointPayment.paid at h
  linarith only [h]

theorem commonCoefficient_pos : 0 < commonCoefficient := by
  norm_num [commonCoefficient, SignedTotalCorrelation.jTwo, SharpJBalance.ninthA,
    SharpJBalance.s, SeventhEighth.sigma, SeventhEighth.alpha]

theorem joint_payment :
    jointPacket log log ≤ jointPacket splitLower splitUpper := by
  have h0 := (split_bounds (by norm_num : (1 : ℝ) ≤ 4/3)).2
  have h1 := (split_bounds (by norm_num : (1 : ℝ) ≤ 3/2)).2
  have hc := mul_le_mul_of_nonneg_left (add_le_add h0 h1) commonCoefficient_pos.le
  have h2 := (split_bounds (by norm_num : (1 : ℝ) ≤ 2654/2181)).2
  have h3 := (split_bounds (by norm_num : (1 : ℝ) ≤ 5781/5308)).2
  have h4 := (split_bounds (by norm_num : (1 : ℝ) ≤ 1800/1327)).1
  have h5 := (split_bounds (by norm_num : (1 : ℝ) ≤ 1327/1200)).2
  have h6 := (split_bounds (by norm_num : (1 : ℝ) ≤ 3681/2654)).2
  have h7 := (split_bounds (by norm_num : (1 : ℝ) ≤ 2354/1327)).1
  have h8 := (split_bounds (by norm_num : (1 : ℝ) ≤ 74881/66350)).2
  have h9 := (split_bounds (by norm_num : (1 : ℝ) ≤ 240187/198481)).2
  have h10 := (split_bounds (by norm_num : (1 : ℝ) ≤ 27551/20600)).1
  have h11 := (split_bounds (by norm_num : (1 : ℝ) ≤ 1227/800)).2
  unfold jointPacket
  linarith only [hc, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

def jointCap : ℝ := jointPacket splitLower splitUpper

theorem mixture_le_jointCap :
    (3/5) * JJointEnvelope.upperMass +
      (2/5) * JFourRemainingMagnitude.jLowerReal ≤ jointCap := by
  rw [joint_collection]
  exact joint_payment

theorem jointConstant_exact : jointConstant =
    (-1928635789776442716396818584281773343106664 /
      161784910925932125867554979620939312758935 : ℝ) := by
  unfold jointConstant
  rw [W12.paymentEndpoint_exact, U8ActualThreshold.gainLower_exact]
  norm_num [SignedTotalCorrelation.jTwo, SharpJBalance.ninthA, SharpJBalance.s,
    SeventhEighth.sigma, SeventhEighth.alpha, V, upperLog, lowerLog, JJointPayment.paid]

end WuTarget.E08Debit
