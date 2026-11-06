import QtwoWholeLower

namespace QtwoWholeCertificate
open Real Wu2008DoubleSieve PositiveCoreResume PositiveSecondPayment
open FixedCoefficientUpperEnclosure (a b)
open QtwoWholeLower
noncomputable section


def correction : ℝ := (QtwoWeightedMoment.gain-GlobalLowerSlack.fifthGain)/4-
  FullAdmissibleStrength.polynomialPayment/4+
  (4*fullSeed*(b-a)^2-fifthHGain)/4+2*(secondGain-BaseHGain.originalGain)

theorem full_correction : rationalFloor = DisjointSlackJoin.coefficient+correction := by
  unfold rationalFloor classicalFloor correction DisjointSlackJoin.coefficient
    GlobalLowerSlack.lowerCoefficient U8ActualThreshold.lowerCoefficient
  ring

theorem gain_exact : QtwoWeightedMoment.gain =
    652164237152789352219420099183809730613098250/30752733541299938654347445560633337363532056907 := by
  rw [gain_exact_relation,GlobalLowerSlack.fifthGain_exact]
  norm_num [QtwoWeightedMoment.meanXY,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]


/-- Fixed exact rational evaluation of the complete new correction; no search. -/
theorem correction_bounds : (1/1000:ℝ) < correction ∧ correction < 2/1000 := by
  unfold correction
  rw [gain_exact,GlobalLowerSlack.fifthGain_exact,FullAdmissibleStrength.polynomial_payment_exact]
  norm_num [fullSeed,fifthHGain,fifthHSeed,secondGain,BaseHGain.originalGain,
    a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem complete_certificate_bounds : (832692/1000000:ℝ) < rationalFloor ∧
    rationalFloor < 833695/1000000 := by
  rw [full_correction]
  constructor <;> linarith only [DisjointSlackJoin.coefficient_bounds.1,
    DisjointSlackJoin.coefficient_bounds.2,correction_bounds.1,correction_bounds.2]

def threshold : ℝ := 8*log (5000/4469)

/-- This is the deficit of this proved rational certificate, not an upper bound
on Qtwo and not a claim that the actual target difference is positive. -/
theorem certificate_shortfall : (3/50:ℝ) < threshold-rationalFloor ∧
    threshold-rationalFloor < 7/100 := by
  have hl := SharpLogRecurrence.log_lower (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have hu := JointLogTotalComparison.log_le_V (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have hlo : (3/50:ℝ)+833695/1000000 < 8*SharpLogRecurrence.lowerLog (5000/4469) := by
    norm_num [SharpLogRecurrence.lowerLog]
  have hup : 8*JointLogTotalComparison.V (5000/4469) < (7/100:ℝ)+832692/1000000 := by
    norm_num [JointLogTotalComparison.V,SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog]
  unfold threshold
  constructor <;> linarith only [hl,hu,hlo,hup,complete_certificate_bounds.1,complete_certificate_bounds.2]

/-- All still-unrounded actual quantities are displayed together. -/
def unpaidMass : ℝ := FeedbackLimit.Cinf/4+
  (fifthGain-4*fullSeed*(b-a)^2)/4+remainder



/-- Full actual lower-count consumer; no independent P2 lower bounds are added. -/
theorem certificate_ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        rationalFloor*U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have he : 0 < (PositiveTwoPayment.Qtwo-rationalFloor)/2 := half_pos (sub_pos.mpr rational_floor)
  obtain ⟨δ,hδ,hd,T,hT,hcount⟩ := PositiveTwoPayment.ordinary_P2 _ he
  refine ⟨δ,hδ,hd,T,hT,fun N hN hEven => ?_⟩
  have hm := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hc : rationalFloor < PositiveTwoPayment.Qtwo-(PositiveTwoPayment.Qtwo-rationalFloor)/2 := by
    linarith only [rational_floor]
  exact (mul_lt_mul_of_pos_right hc hm).trans_le (hcount N hN hEven)

#print axioms QtwoWholeLower.full_floor
#print axioms complete_certificate_bounds
#print axioms certificate_shortfall
#print axioms certificate_ordinary_P2

end
end QtwoWholeCertificate
