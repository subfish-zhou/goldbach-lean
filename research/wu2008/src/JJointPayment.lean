import WidthIntervals

noncomputable section
open Real Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison GlobalSignedActualComparison
namespace JJointPayment

def paid (L H : ℝ → ℝ) : ℝ :=
  (114311567583583563540341792601841747680791898253530810311531720945444318808651217185998477364750392365556807/43017824535733324069161959611446598064430140623688666430097655351517060915657750515605921807214144732088000)+
  (23343409479070814/1325818019511839835)*L (4/3)+
  (23343409479070814/1325818019511839835)*L (3/2)+
  (-106/15)*H (2654/2181)+
  (-112/15)*H (5781/5308)+
  (2/5)*L (1800/1327)+
  (-5/6)*H (1327/1200)+
  (-8/15)*H (3681/2654)+
  (3/10)*L (2354/1327)+
  (-6386323159298400/3273624739535407)*H (74881/66350)+
  (-3496183680/2336752783)*H (240187/198481)+
  (2654/9635)*L (27551/20600)+
  (-224/405)*H (1227/800)

theorem collected (f : ℝ → ℝ) : JJointEnvelope.gainPacket f = paid f f := by
  unfold paid
  norm_num [JJointEnvelope.gainPacket,JJointEnvelope.upperPacket,jLower,SharpJBalance.ninthB,SharpJBalance.ninthC,SharpJBalance.ninthD,JCorrelatedResidualTight.C,JCorrelatedResidualTight.R,
    JCubicPrimitive.rationalPart,JCubicPrimitive.crossRatio,SharpJBalance.a,SharpJBalance.s,
    SharpJBalance.b,ninthProfileK2,SeventhEighth.sigma,SeventhEighth.alpha,
    UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,UnroundedPayments.j8Upper,
    UnroundedPayments.j9Upper,SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,
    JointJLossStrength.fixedRecovery,JointJLossStrength.massPayment,upperLog,lowerLog]
  ring

theorem lower_payment : paid lowerLog V ≤ JJointEnvelope.gainPacket log := by
  rw [collected]
  have l0 := log_lower (by norm_num : (1:ℝ) ≤ (5781/5308))
  have h0 := log_le_V (by norm_num : (1:ℝ) ≤ (5781/5308))
  have l1 := log_lower (by norm_num : (1:ℝ) ≤ (1327/1200))
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ (1327/1200))
  have l2 := log_lower (by norm_num : (1:ℝ) ≤ (74881/66350))
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ (74881/66350))
  have l3 := log_lower (by norm_num : (1:ℝ) ≤ (240187/198481))
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ (240187/198481))
  have l4 := log_lower (by norm_num : (1:ℝ) ≤ (2654/2181))
  have h4 := log_le_V (by norm_num : (1:ℝ) ≤ (2654/2181))
  have l5 := log_lower (by norm_num : (1:ℝ) ≤ (4/3))
  have h5 := log_le_V (by norm_num : (1:ℝ) ≤ (4/3))
  have l6 := log_lower (by norm_num : (1:ℝ) ≤ (27551/20600))
  have h6 := log_le_V (by norm_num : (1:ℝ) ≤ (27551/20600))
  have l7 := log_lower (by norm_num : (1:ℝ) ≤ (1800/1327))
  have h7 := log_le_V (by norm_num : (1:ℝ) ≤ (1800/1327))
  have l8 := log_lower (by norm_num : (1:ℝ) ≤ (3681/2654))
  have h8 := log_le_V (by norm_num : (1:ℝ) ≤ (3681/2654))
  have l9 := log_lower (by norm_num : (1:ℝ) ≤ (3/2))
  have h9 := log_le_V (by norm_num : (1:ℝ) ≤ (3/2))
  have l10 := log_lower (by norm_num : (1:ℝ) ≤ (1227/800))
  have h10 := log_le_V (by norm_num : (1:ℝ) ≤ (1227/800))
  have l11 := log_lower (by norm_num : (1:ℝ) ≤ (2354/1327))
  have h11 := log_le_V (by norm_num : (1:ℝ) ≤ (2354/1327))
  unfold paid
  linarith only [l0,h0,l1,h1,l2,h2,l3,h3,l4,h4,l5,h5,l6,h6,l7,h7,l8,h8,l9,h9,l10,h10,l11,h11]

def gain : ℝ := paid lowerLog V

theorem gain_bounds : (2639/1000000:ℝ) < gain ∧ gain < 2640/1000000 := by
  norm_num [gain,paid,lowerLog,upperLog,V]

theorem gain_pos : 0 < gain := lt_trans (by norm_num) gain_bounds.1

/-- Replace the previous J recovery; no other block pays for this gain. -/
theorem j_block_payment : gain ≤
    (GlobalLowerSlack.jSlack+GlobalLowerSlack.jPaymentSlack)/4 := by
  have hp := lower_payment
  have he := JJointEnvelope.gain_packet_identity
  have hj := JJointEnvelope.j_loss_lower
  unfold gain GlobalLowerSlack.jSlack GlobalLowerSlack.jPaymentSlack
  linarith only [hp,he,hj]

theorem other_payment : gain ≤ SixthRetainedSlack.otherRemainder := by
  obtain ⟨_,_,_,_,_,_,_,h5r,_,_,h4⟩ := GlobalLowerSlack.component_nonnegative
  have hf := GlobalLowerSlack.fifth_gain_paid
  have ha := GlobalLowerSlack.payment_nonnegative.1
  have hg := FullAdmissibleStrength.polynomial_payment
  have hu := U8ActualThreshold.exact_weight_gain_bounds.1
  have hj := j_block_payment
  unfold SixthRetainedSlack.otherRemainder
  linarith only [h5r,h4,hf,ha,hg,hu,hj]

def coefficient : ℝ := DisjointSlackJoin.coefficient+gain

theorem actual_lower : coefficient < U8CanonicalMother.improvedCoefficient := by
  have he := DisjointSlackJoin.remaining_identity
  have hs := BaseSharedSlack.block_payment
  have hb := SixthRetainedSlack.block_buffer_positive
  have hj := other_payment
  unfold coefficient
  linarith only [he,hs,hb,hj]

theorem strict_ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        coefficient*U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hp : 0 < (U8CanonicalMother.improvedCoefficient-coefficient)/2 :=
    half_pos (sub_pos.mpr actual_lower)
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := U8CanonicalMother.improved_ordinary_P2 _ hp
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 < U8CanonicalMother.M N := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hc : coefficient < U8CanonicalMother.improvedCoefficient-
      (U8CanonicalMother.improvedCoefficient-coefficient)/2 := by linarith only [hp]
  exact (mul_lt_mul_of_pos_right hc hs).trans_le (h N hN he)

theorem coefficient_bounds : (834331/1000000:ℝ) < coefficient ∧ coefficient < 834335/1000000 := by
  unfold coefficient
  constructor <;> linarith only [DisjointSlackJoin.coefficient_bounds.1,
    DisjointSlackJoin.coefficient_bounds.2,gain_bounds.1,gain_bounds.2]

theorem certificate_below_target : coefficient < 8*log (5000/4469) := by
  have hl := log_lower (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have hc : (834335/1000000:ℝ) < 8*lowerLog (5000/4469) := by norm_num [lowerLog]
  linarith only [coefficient_bounds.2,hl,hc]

theorem rational_corridor : (834331/1000000:ℝ) < U8CanonicalMother.improvedCoefficient ∧
    U8CanonicalMother.improvedCoefficient < 911612/1000000 :=
  ⟨coefficient_bounds.1.trans actual_lower,CorrectedCoefficientUpper.rational_actual_corridor.2⟩

end JJointPayment
