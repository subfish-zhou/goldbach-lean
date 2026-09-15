import PositiveTwoMother

namespace PositiveTwoPayment
open Wu2008DoubleSieve Real U8CanonicalMother PositiveCoreResume PositiveSecondPayment
noncomputable section

/-- A coefficient whose actual validity is proved from the two count producers below. -/
def Qof (g2 g5 : ℝ) : ℝ := FeedbackLimit.Qinf + increment g2 g5/4

theorem signed_count {g2 g5 : ℝ} (counts : PositiveCounts g2 g5) {δ ε : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-FullSourceLog.GammaLog6+
        increment g2 g5+8*L-8*I-ε)*U8CanonicalMother.M N ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have hε3 : 0 < ε/3 := by positivity
  obtain ⟨Tr,hTr,hr⟩ := ordinary_rebuilt counts hδ hd hε3
  obtain ⟨T6,_,h6⟩ := FeedbackLimit.supplied_sixth (ε/3) hε3
  obtain ⟨Ts,hs⟩ := OriginalU8.Weighted.physicalSmall_original_integral (ε/3) hε3
  refine ⟨max Tr (max T6 Ts),by omega,fun N hN he => ?_⟩
  have hrN := hr N (by omega) he
  have h6N := h6 N (by omega) he
  have hsN := hs N (by omega) he
  have hnorm := scale_eq_liu (show 0 < N by omega)
  rw [← small_eq_physicalSmall] at hsN
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤ (8*I+ε/3)*U8CanonicalMother.M N := by
    rw [hnorm]
    convert hsN using 1
    ring
  unfold SixthSlotCore.remainderCoefficient at hrN
  rw [← L_eq_oldSmallIntegral] at hrN
  dsimp [U8CanonicalMother.M] at hsM ⊢
  ring_nf at hrN h6N hsM ⊢
  linarith only [hrN,h6N,hsM]

/-- Full positive gain, with arbitrary eta and the same original delta/common threshold contract. -/
theorem ordinary_of_counts {g2 g5 : ℝ} (counts : PositiveCounts g2 g5) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qof g2 g5-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hd,hcoef⟩ := SixthSlotAssembly.coefficient_payment FeedbackLimit.Cinf
    (show 0 < 4*η by positivity)
  obtain ⟨T,hT,hcount⟩ := signed_count counts hδ hd (show 0 < (4*η)/3 by positivity)
  refine ⟨δ,hδ,hd,T,hT,fun N hN he => ?_⟩
  have hc := hcount N hN he
  have hm0 : 0 ≤ U8CanonicalMother.M N := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  have hcoef' : 4*Qof g2 g5-4*η ≤
      FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-FullSourceLog.GammaLog6+
        increment g2 g5+8*L-8*I-(4*η)/3 := by
    unfold Qof FeedbackLimit.Qinf SixthSlotAssembly.Q at *
    linarith only [hcoef]
  have hm := (mul_le_mul_of_nonneg_right hcoef' hm0).trans hc
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hm
  nlinarith only [hm]

/-- The two fully paid improvements, with the old positive coefficient used only for comparison. -/
def Qtwo : ℝ := Qpositive + 2*(secondGain-BaseHGain.originalGain)

theorem Qtwo_eq_Qof : Qtwo = Qof secondGain fifthGain := by
  unfold Qtwo Qof Qpositive increment fifthIncrement
  ring

theorem Qtwo_strict : Qpositive < Qtwo := by
  unfold Qtwo
  linarith only [secondGain_strict]

/-- The concrete endpoint: both actual producers are constructed, not assumed. -/
theorem ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qtwo-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  rw [Qtwo_eq_Qof]
  exact ordinary_of_counts two_counts η hη

/-- A fixed endpoint strictly above the previous full-F5 endpoint. -/
def paidEndpoint : ℝ := Qpositive+(secondGain-BaseHGain.originalGain)

theorem paidEndpoint_strict : Qpositive < paidEndpoint := by
  unfold paidEndpoint
  linarith only [secondGain_strict]

/-- Half the newly available F2 increment is paid while all of the F5 gain is retained. -/
theorem paid_above_Qpositive :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        paidEndpoint*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have he : 0 < secondGain-BaseHGain.originalGain := sub_pos.mpr secondGain_strict
  obtain ⟨δ,hδ,hd,T,hT,hcount⟩ := ordinary_P2 _ he
  refine ⟨δ,hδ,hd,T,hT,fun N hN hEven => ?_⟩
  have h := hcount N hN hEven
  convert h using 1
  unfold Qtwo paidEndpoint
  ring

end
end PositiveTwoPayment
