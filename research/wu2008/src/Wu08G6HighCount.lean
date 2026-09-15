import Wu08G6HighLoss
import PositiveTwoP2

/-! The full-domain expression minus its *own* high-domain loss is paid by the
existing actual sixth producer, with the classical F6 unchanged. -/
namespace Wu08G6High
open Set MeasureTheory QuarterTrim DirectFiniteF6 Wu2008DoubleSieve ActualNineFeedback
open scoped Classical
noncomputable section

/-- Finite n first; then shrink t>0 and positive delta. Both old debits stay. -/
theorem finite_exact_payment {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2) (n : ℕ) :
    published (transferredLower n) - highLoss (transferredLower n) -
      loss (transferredLower n)*t - deltaLoss δ*E n ≤ truncatedSixthLowerHadmdelta δ := by
  rw [published_eq_legal_add_high]
  convert finite_Gamma_payment ht ht' hd hdt n using 1
  unfold C
  ring

/-- This version has a proved finite-height loss cap; no high-source axiom. -/
theorem finite_capped_payment {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hd : 0 < δ) (hdt : δ ≤ t/2) (n : ℕ) :
    published (transferredLower n) - (16129:ℝ)/40000*heightCap (transferredLower n) -
      loss (transferredLower n)*t - deltaLoss δ*E n ≤ truncatedSixthLowerHadmdelta δ := by
  have hp := finite_exact_payment ht ht' hd hdt n
  have hl := highLoss_le_heightCap (transferredLower n)
  linarith only [hp,hl]

/-- Original Theta normalization and the same full classical F6 are inherited.
The high integral is debited, not asserted to be an actual h contribution. -/
theorem supplied_sixth_exact :
    SixthSlotAssembly.SixthLower (published FeedbackLimit.Winf - highLoss FeedbackLimit.Winf) := by
  have he : published FeedbackLimit.Winf - highLoss FeedbackLimit.Winf = FeedbackLimit.Cinf := by
    rw [published_eq_legal_add_high]
    unfold FeedbackLimit.Cinf
    ring
  rw [he]
  exact FeedbackLimit.supplied_sixth

theorem supplied_sixth_capped : SixthSlotAssembly.SixthLower
    (published FeedbackLimit.Winf - (16129:ℝ)/40000*heightCap FeedbackLimit.Winf) := by
  intro ε hε
  obtain ⟨T,hT,hcount⟩ := FeedbackLimit.supplied_sixth ε hε
  refine ⟨T,hT,fun N hN he => ?_⟩
  have hc := legal_lower FeedbackLimit.Winf
  change _ ≤ FeedbackLimit.Cinf at hc
  have hm := mul_le_mul_of_nonneg_right
    (show truncatedSixthLowerF6lin+published FeedbackLimit.Winf-
      (16129:ℝ)/40000*heightCap FeedbackLimit.Winf-ε ≤
      truncatedSixthLowerF6lin+FeedbackLimit.Cinf-ε by linarith only [hc])
    (truncatedSixthClosure_scale_nonneg (show 4 ≤ N by omega))
  have hm' : (truncatedSixthLowerF6lin+(published FeedbackLimit.Winf-
      (16129:ℝ)/40000*heightCap FeedbackLimit.Winf)-ε)*wuSingularSeries N*N/Real.log N^(2:ℕ) ≤
      (truncatedSixthLowerF6lin+FeedbackLimit.Cinf-ε)*wuSingularSeries N*N/Real.log N^(2:ℕ) := by
    simpa only [truncatedSixthMassScale,mul_div_assoc,mul_assoc,sub_eq_add_neg,add_assoc] using hm
  exact hm'.trans (hcount N hN he)

/-- Analytic full-domain target in the *same* two-positive-slot mother.
This number alone is NOT claimed to be a lower bound for P2. -/
def Qpublished : ℝ := PositiveTwoPayment.Qtwo +
  (published FeedbackLimit.Winf-FeedbackLimit.Cinf)/4

/-- Full replacement expanded: only the sixth slot changes, once. -/
theorem Qpublished_same_mother :
    Qpublished = LogP2.Qlog + (published FeedbackLimit.Winf-FullSourceLog.GammaLog6+
      PositiveTwoPayment.increment PositiveSecondPayment.secondGain PositiveCoreResume.fifthGain)/4 := by
  rw [Qpublished,PositiveTwoPayment.Qtwo_eq_Qof]
  unfold PositiveTwoPayment.Qof FeedbackLimit.Qinf
  ring

/-- The exact debit recovers the actually paid coefficient, not a difference
between unrelated estimates of Q. -/
theorem Qtwo_exact :
    PositiveTwoPayment.Qtwo = Qpublished-highLoss FeedbackLimit.Winf/4 := by
  have h := published_eq_legal_add_high FeedbackLimit.Winf
  change published FeedbackLimit.Winf = FeedbackLimit.Cinf+highLoss FeedbackLimit.Winf at h
  unfold Qpublished
  linarith only [h]

def Qcapped : ℝ := Qpublished-(16129:ℝ)/160000*heightCap FeedbackLimit.Winf

theorem Qcapped_le_Qtwo : Qcapped ≤ PositiveTwoPayment.Qtwo := by
  have h := highLoss_le_heightCap FeedbackLimit.Winf
  rw [Qtwo_exact]
  unfold Qcapped
  linarith only [h]

/-- Honest actual ordinary-P2 lower bound, all gains in the original mother,
positive delta and common threshold; no artificial numerical table premise. -/
theorem ordinary_P2_capped (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qcapped-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hd,hd',T,hT,hcount⟩ := PositiveTwoPayment.ordinary_P2 η hη
  refine ⟨δ,hd,hd',T,hT,fun N hN he => ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right Qcapped_le_Qtwo η)
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le).trans (hcount N hN he)

#print axioms finite_capped_payment
#print axioms supplied_sixth_exact
#print axioms ordinary_P2_capped
end
end Wu08G6High
