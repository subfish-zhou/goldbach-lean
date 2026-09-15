import PositiveCoreMother

namespace PositiveCoreResume
open Wu2008DoubleSieve Real U8CanonicalMother
noncomputable section

/-- Changed actual positive input; this is not a new upper package for fixed Qinf. -/
def Qpositive : ℝ := FeedbackLimit.Qinf + fifthIncrement/4

theorem Qpositive_strict : FeedbackLimit.Qinf < Qpositive := by
  unfold Qpositive
  linarith only [fifthIncrement_pos]

theorem signed_count {δ ε : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-FullSourceLog.GammaLog6+
        fifthIncrement+8*L-8*I-ε)*U8CanonicalMother.M N ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have hε3 : 0 < ε/3 := by positivity
  obtain ⟨Tr,hTr,hr⟩ := ordinary_rebuilt hδ hd hε3
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
theorem ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qpositive-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hd,hcoef⟩ := SixthSlotAssembly.coefficient_payment FeedbackLimit.Cinf
    (show 0 < 4*η by positivity)
  obtain ⟨T,hT,hcount⟩ := signed_count hδ hd (show 0 < (4*η)/3 by positivity)
  refine ⟨δ,hδ,hd,T,hT,fun N hN he => ?_⟩
  have hc := hcount N hN he
  have hm0 : 0 ≤ U8CanonicalMother.M N := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  have hcoef' : 4*Qpositive-4*η ≤
      FullLogMother.psiCoefficient δ+FeedbackLimit.Cinf-FullSourceLog.GammaLog6+
        fifthIncrement+8*L-8*I-(4*η)/3 := by
    unfold Qpositive FeedbackLimit.Qinf SixthSlotAssembly.Q at *
    linarith only [hcoef]
  have hm := (mul_le_mul_of_nonneg_right hcoef' hm0).trans hc
  change _ ≤ 4*((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
    ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) at hm
  nlinarith only [hm]

/-- A fixed positive part of the new gain is actually paid, rather than merely displayed. -/
theorem paid_above_old_limit :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (FeedbackLimit.Qinf+fifthIncrement/8)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have he : 0 < fifthIncrement/8 := div_pos fifthIncrement_pos (by norm_num)
  obtain ⟨δ,hδ,hd,T,hT,hcount⟩ := ordinary_P2 _ he
  refine ⟨δ,hδ,hd,T,hT,fun N hN hEven => ?_⟩
  have h := hcount N hN hEven
  convert h using 1
  unfold Qpositive
  ring

/-- Exact remaining positive comparison, with no assertion that its right-hand side holds. -/
theorem target_iff_fifth_gap :
    8*log (5000/4469) < Qpositive ↔
      4*(8*log (5000/4469)-FeedbackLimit.Qinf) < fifthGain-fifthHGain := by
  unfold Qpositive fifthIncrement
  constructor <;> intro h <;> linarith only [h]

end
end PositiveCoreResume
