import JointHMotherCount
import Phase25Audit

namespace Wu2008DoubleSieve.JointHMotherPayment
open Real SingleUpperHIntegral HighSixDeltaLimit
noncomputable section

/-- The old signed coefficient is identified algebraically, not used as a count lower. -/
theorem fixed_coefficient_identity (δ : ℝ) :
    JointHMother.psiCoefficient δ = HighSixLowHMother.psiCoefficient δ +
      (8*BaseHGain.originalGain+fifthHGain) := by
  unfold JointHMother.psiCoefficient HighSixLowHMother.psiCoefficient
  ring

theorem fixed_same_mother_identity (δ : ℝ) :
    JointHMother.psiCoefficient δ = HighSixPsiMother.psiCoefficient δ + gainH34 δ +
      (8*BaseHGain.originalGain+fifthHGain) := by
  rw [fixed_coefficient_identity, ParentPhase9HalfWeightCount.same_mother_identity]

/-- Only the original fixed HighSix window and the original F18 H producer occur.
The F2 gain is already inside the newly reconstructed finite signed count. -/
theorem same_mother_delta_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (limitCoefficient+4*Phase18.g18+(8*BaseHGain.originalGain+fifthHGain)-ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have herror := Phase18.B18_pos
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,ha1,hclose⟩ := coefficient_close he
  let δ : ℝ := min (a/2) (ε/(12*(Phase18.B18+1)))
  have hδ : 0 < δ := lt_min (half_pos ha) (div_pos hε (by positivity))
  have hδa : δ < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hδhi : δ ≤ 1/100 := hδa.le.trans ha1
  have hδb : δ ≤ ε/(12*(Phase18.B18+1)) := min_le_right _ _
  have hpay : 12*(Phase18.B18+1)*δ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*(Phase18.B18+1))).mp hδb
    nlinarith only [hh]
  have hbudget : 4*Phase18.B18*δ ≤ ε/3 := by nlinarith only [hpay,hδ]
  have hcoef := (abs_lt.mp (hclose δ hδ hδa)).1
  have hh := Phase18.gain18_linear_error hδ hδhi
  obtain ⟨T,hT,hcount⟩ := JointHMother.actual_count_lower hδ hδhi he
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN heven
  have hm := hcount N hN heven
  rw [fixed_same_mother_identity] at hm
  have hc : limitCoefficient+4*Phase18.g18+(8*BaseHGain.originalGain+fifthHGain)-ε ≤
      HighSixPsiMother.psiCoefficient δ+gainH34 δ+(8*BaseHGain.originalGain+fifthHGain)-ε/3 := by
    linarith only [hcoef,hh,hbudget]
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hp := mul_le_mul_of_nonneg_right hc hs
  calc
    _ = (limitCoefficient+4*Phase18.g18+(8*BaseHGain.originalGain+fifthHGain)-ε)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ (HighSixPsiMother.psiCoefficient δ+gainH34 δ+(8*BaseHGain.originalGain+fifthHGain)-ε/3)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
    _ = (HighSixPsiMother.psiCoefficient δ+gainH34 δ+(8*BaseHGain.originalGain+fifthHGain)-ε/3)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := hm

/-- New genuinely unrounded family. The old Q and L25 definitions remain unchanged. -/
def unroundedCoefficient : ℝ := Phase20.unroundedCoefficient+(2*BaseHGain.originalGain+fifthHGain/4)

def lowerCoefficient : ℝ := Phase25.lowerCoefficient+(2*BaseHGain.originalGain+fifthHGain/4)

theorem unrounded_coefficient_identity : unroundedCoefficient =
    TruncatedElevenClassicalCountLower.classicalCoefficient/4 + Phase20.rawPsi +
      Phase18.g18 + (2*BaseHGain.originalGain+fifthHGain/4) := by
  rw [unroundedCoefficient,Phase20.unrounded_coefficient_identity]

theorem unrounded_strict_improvement : Phase20.unroundedCoefficient < unroundedCoefficient := by
  unfold unroundedCoefficient
  linarith only [BaseHGain.originalGain_pos, fifthHGain_pos]

theorem lower_strict_improvement : Phase25.lowerCoefficient < lowerCoefficient := by
  unfold lowerCoefficient
  linarith only [BaseHGain.originalGain_pos, fifthHGain_pos]

/-- Common threshold for the source and the literal unrestricted ordinary-P2 count.
No old ordinary-count lower bound is invoked anywhere in this new count chain. -/
theorem unrounded_ordinary_P2_same_threshold (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
        ((unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := same_mother_delta_payment (show 0 < 4*η by positivity)
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  have hp : (unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    have hid : (unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) =
        ((limitCoefficient+4*Phase18.g18+(8*BaseHGain.originalGain+fifthHGain)-4*η)*
          wuSingularSeries N*N/log N^(2 : ℕ))/4 := by
      unfold unroundedCoefficient Phase20.unroundedCoefficient
      ring
    rw [hid]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])
  exact ⟨hp,hp⟩

/-- The SAME positive payment margin Q-L25 suffices; it is not consumed twice. -/
theorem payment_gap_identity :
    unroundedCoefficient-lowerCoefficient = Phase25.paymentEta := by
  unfold unroundedCoefficient lowerCoefficient Phase25.paymentEta
  ring

theorem payment_gap_pos : 0 < unroundedCoefficient-lowerCoefficient := by
  rw [payment_gap_identity]
  exact Phase25.paymentEta_pos

theorem payment_identity : unroundedCoefficient-Phase25.paymentEta = lowerCoefficient := by
  unfold unroundedCoefficient lowerCoefficient Phase25.paymentEta
  ring

/-- Full L25+2g payment from the NEW Q+2g-eta family at eta=Q-L25. -/
theorem full_ordinary_P2_same_threshold :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (lowerCoefficient*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
        (lowerCoefficient*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  simpa only [payment_identity] using
    unrounded_ordinary_P2_same_threshold Phase25.paymentEta Phase25.paymentEta_pos

end
end Wu2008DoubleSieve.JointHMotherPayment
