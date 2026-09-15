import GlobalLowerSlack

/-! Disjoint classical-sixth and retained-payment recovery.
The new Gamma6 correction is not part of this block. -/
noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
namespace SixthRetainedSlack

/-- Keep the unrounded rational consequence of the frozen C18 lower bound. -/
def gFloor : ℝ := (1071/10000)*HighSixPhase9.sourceP

/-- Keep the exact old prime-window lower payment, without decimal rounding. -/
def psiFloor : ℝ := HighSixPhase9.sourceP*
  ((HighSix.right-HighSix.left)/(HighSix.left*(1/2-HighSix.left)))-Phase20.fixedPsi

/-- This fixed rational payment uses only the retained block. -/
def gain : ℝ := gFloor+psiFloor-3/10000

/-- The old feedback denominator leaves strictness after the rational payment. -/
theorem gFloor_lt : gFloor < Phase18.g18 := by
  have hd := sub_pos.mpr Phase17.rhoCoupled_bounds.2
  have hp : 0 < HighSixPhase9.sourceP := by norm_num [HighSixPhase9.sourceP]
  have hl := mul_lt_mul_of_pos_right PsiG18Strength.C18_bounds.1 hp
  have hf : 0 < gFloor := mul_pos (by norm_num) hp
  unfold Phase18.g18
  apply (lt_div_iff₀ hd).2
  change gFloor < Phase18.C18*HighSixPhase9.sourceP at hl
  have hr := mul_pos hf Phase17.rhoCoupled_bounds.1
  nlinarith only [hl,hr]

/-- Both factors are the already frozen literal Psi and prime integral. -/
theorem psiFloor_le : psiFloor ≤ Phase20.psiPaymentLoss := by
  have hp := HighSixPhase5.psi_lower
  have h := mul_le_mul hp PsiG18Strength.prime_integral_bounds.1
    (by norm_num [HighSix.left,HighSix.right]) HighSixPhase5.psi_positive.le
  unfold psiFloor Phase20.psiPaymentLoss Phase20.rawPsi
  norm_num [HighSixPhase9.sourceP,HighSix.left,HighSix.right,HighSix.s,HighSix.S] at h ⊢
  linarith only [h]

theorem gain_exact : gain =
    164850980773131214445722537/189822513390888284615241000000000 := by
  norm_num [gain,gFloor,psiFloor,HighSixPhase9.sourceP,HighSix.left,HighSix.right,Phase20.fixedPsi]

theorem gain_positive : 0 < gain := by rw [gain_exact]; norm_num

/-- A small but genuinely positive rational payment, not a strict-zero placeholder. -/
theorem gain_bounds : (86/100000000:ℝ) < gain ∧ gain < 87/100000000 := by
  rw [gain_exact]; norm_num

theorem retained_strict : gain < GlobalLowerSlack.retainedPaymentSlack := by
  unfold gain GlobalLowerSlack.retainedPaymentSlack
  linarith only [gFloor_lt,psiFloor_le]

/-- Exactly the assigned old sixth and retained block, before any Gamma6 term. -/
def block : ℝ := AnalyticTotalThreshold.sixthLoss/4+GlobalLowerSlack.retainedPaymentSlack

theorem block_identity : block = GlobalLowerSlack.sixthLogSlack/4+
    GlobalLowerSlack.sixthRecurrence/4+GlobalLowerSlack.retainedPaymentSlack := by
  unfold block
  rw [← GlobalLowerSlack.sixth_slack_identity]
  ring

/-- No quantified recurrence gain is claimed: its full old cap is kept separately. -/
theorem classical_sixth_bounds : 0 ≤ GlobalLowerSlack.sixthLogSlack ∧
    0 ≤ GlobalLowerSlack.sixthRecurrence ∧ GlobalLowerSlack.sixthRecurrence < 1/100000 :=
  ⟨sub_nonneg.mpr ClassicalLossBottleneck.sixth_endpoint_le_logIntegral,
    ClassicalLossBottleneck.sixth_recurrence_integral_cap⟩

/-- Strictness is local to this block; no other positive summand is borrowed. -/
theorem strict_block_payment : gain < block := by
  rw [block_identity]
  have hs := classical_sixth_bounds
  linarith only [retained_strict,hs.1,hs.2.1]

/-- The other worker's block is exposed unchanged, with no payment taken here. -/
def sharedBlock : ℝ := (AnalyticTotalThreshold.baseLoss+GlobalLowerSlack.highSlack+
  GlobalLowerSlack.middleSlack+BaseGSharedActualRecovery.lowKernel)/4

/-- Only nonnegativity is used from these unpaid, unassigned terms. -/
def otherRemainder : ℝ := (GlobalLowerSlack.jSlack+GlobalLowerSlack.jPaymentSlack+
  (GlobalLowerSlack.fifthLogSlack-GlobalLowerSlack.fifthGain)+GlobalLowerSlack.fifthRecurrence+
  GlobalLowerSlack.fourSlack+GlobalLowerSlack.analyticPaymentSlack)/4+
  (FullAdmissibleSeed.Gamma6-FullAdmissibleStrength.polynomialPayment)/4+
  (2*(U8CanonicalMother.L-U8CanonicalMother.I)-U8ActualThreshold.gainLower)

theorem shared_nonnegative : 0 ≤ sharedBlock := by
  obtain ⟨hb,hh,hm,hl,_⟩ := GlobalLowerSlack.component_nonnegative
  unfold sharedBlock
  linarith only [hb,hh,hm,hl]

theorem other_nonnegative : 0 ≤ otherRemainder := by
  obtain ⟨_hb,_hh,_hm,_hl,hj,hjp,_h5,h5r,_h6,_h6r,h4⟩ :=
    GlobalLowerSlack.component_nonnegative
  have hf := GlobalLowerSlack.fifth_gain_paid
  have ha := GlobalLowerSlack.payment_nonnegative.1
  have hg := FullAdmissibleStrength.polynomial_payment
  have hu := U8ActualThreshold.exact_weight_gain_bounds.1
  unfold otherRemainder
  linarith only [hj,hjp,h5r,h4,hf,ha,hg,hu]

/-- This is the exact disjoint partition of the parent's remaining identity. -/
theorem unpaid_partition : GlobalLowerSlack.unpaid = sharedBlock+block+otherRemainder := by
  rw [block_identity]
  unfold GlobalLowerSlack.unpaid GlobalLowerSlack.realSlack sharedBlock otherRemainder
  ring

/-- The exact parent identity is genuinely consumed, not supplied as a hypothesis. -/
theorem actual_partition : U8CanonicalMother.improvedCoefficient-GlobalLowerSlack.lowerCoefficient =
    sharedBlock+block+otherRemainder := by
  rw [GlobalLowerSlack.actual_remaining_identity,unpaid_partition]

def lowerCoefficient : ℝ := GlobalLowerSlack.lowerCoefficient+gain

theorem actual_lower : lowerCoefficient < U8CanonicalMother.improvedCoefficient := by
  have he := actual_partition
  unfold lowerCoefficient
  linarith only [he,strict_block_payment,shared_nonnegative,other_nonnegative]

/-- A composable theorem: the sibling may spend its own non-strict block bound.
Strictness here is supplied only by strict_block_payment. -/
theorem combine_shared {c : ℝ} (hc : c ≤ sharedBlock) :
    GlobalLowerSlack.lowerCoefficient+c+gain < U8CanonicalMother.improvedCoefficient := by
  linarith only [actual_partition,hc,strict_block_payment,other_nonnegative]

theorem strict_improvement : GlobalLowerSlack.lowerCoefficient < lowerCoefficient := by
  unfold lowerCoefficient
  linarith only [gain_positive]

/-- The remaining block buffer is strictly positive even after paying gain. -/
theorem remaining_identity : U8CanonicalMother.improvedCoefficient-lowerCoefficient =
    sharedBlock+(block-gain)+otherRemainder := by
  have he := actual_partition
  unfold lowerCoefficient
  linarith only [he]

theorem block_buffer_positive : 0 < block-gain := sub_pos.mpr strict_block_payment

/-- Literal common ordinary P2, with 1 allowed and 0 excluded in the complement. -/
theorem strict_ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        lowerCoefficient*U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hp : 0 < (U8CanonicalMother.improvedCoefficient-lowerCoefficient)/2 :=
    half_pos (sub_pos.mpr actual_lower)
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := U8CanonicalMother.improved_ordinary_P2 _ hp
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 < U8CanonicalMother.M N := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hc : lowerCoefficient < U8CanonicalMother.improvedCoefficient-
      (U8CanonicalMother.improvedCoefficient-lowerCoefficient)/2 := by linarith only [hp]
  exact (mul_lt_mul_of_pos_right hc hs).trans_le (h N hN he)

/-- This payment does not prove the target; it does strictly improve the true lower bound. -/
theorem certificate_below_target : lowerCoefficient < 8*log (5000/4469) := by
  have hl := SharpLogRecurrence.log_lower (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have hc : (831354/1000000:ℝ)+87/100000000 < 8*SharpLogRecurrence.lowerLog (5000/4469) := by
    norm_num [SharpLogRecurrence.lowerLog]
  unfold lowerCoefficient
  linarith only [GlobalLowerSlack.lowerCoefficient_bounds.2,gain_bounds.2,hc,hl]

end SixthRetainedSlack
