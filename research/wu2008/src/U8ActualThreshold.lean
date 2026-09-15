import U8CanonicalMother
import FifthReciprocalAffineUpper
import FullAdmissibleStrength

/-! Exact rational-weight integration on the unchanged small interval.
Only the previously fixed log package is used.  No target comparison is assumed. -/
noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve
namespace U8ActualThreshold
open OriginalU8.SymbolicSmallGain (a b a_lt_b)
open SharpLogRecurrence (lowerLog upperLog)
open JointLogTotalComparison (V)

def ratio : ℝ := b*(1-a)/(a*(1-b))
def weight (t : ℝ) : ℝ := (b-t)/(t*(1-t)^2)
def primitive (t : ℝ) : ℝ := b*(log t-log (1-t))+(b-1)/(1-t)
def weightMass : ℝ := b*log ratio-(b-a)/(1-a)
def weightLower : ℝ := b*lowerLog ratio-(b-a)/(1-a)
def weightUpper : ℝ := b*V ratio-(b-a)/(1-a)
def gainLower : ℝ := 2*lowerLog (2-3*b)*weightLower
def gainUpper : ℝ := 2*V (2-3*a)*weightUpper

theorem domain {t : ℝ} (ht : t ∈ Icc a b) :
    0 < t ∧ 0 < 1-t ∧ 0 ≤ b-t := by
  dsimp [a,b] at ht ⊢
  constructor
  · linarith [ht.1]
  constructor <;> linarith [ht.2]

theorem weight_nonneg {t : ℝ} (ht : t ∈ Icc a b) : 0 ≤ weight t := by
  obtain ⟨hp,hq,hr⟩ := domain ht
  exact div_nonneg hr (mul_pos hp (sq_pos_of_pos hq)).le

theorem weight_integrable : IntervalIntegrable weight volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  rw [uIcc_of_le a_lt_b.le] at ht
  obtain ⟨hp,hq,_⟩ := domain ht
  exact (mul_pos hp (sq_pos_of_pos hq)).ne'

theorem primitive_derivative {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivAt primitive (weight t) t := by
  obtain ⟨hp,hq,_⟩ := domain ht
  have h := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  convert (((Real.hasDerivAt_log hp.ne').sub (h.log hq.ne')).const_mul b).add
    ((hasDerivAt_const t (b-1)).div h hq.ne') using 1 <;>
    first | rfl | (dsimp [primitive,weight]; field_simp; ring)

theorem weight_integral : (∫ t in a..b, weight t) = weightMass := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := primitive) (f' := weight)
    (fun t ht => primitive_derivative (by
      rw [uIcc_of_le a_lt_b.le] at ht
      exact ht)) weight_integrable
  rw [hi]
  have ha : (a : ℝ) ≠ 0 := by norm_num [a]
  have hb : (b : ℝ) ≠ 0 := by norm_num [b]
  have hac : (1-a : ℝ) ≠ 0 := by norm_num [a]
  have hbc : (1-b : ℝ) ≠ 0 := by norm_num [b]
  unfold primitive weightMass ratio
  rw [log_div (mul_ne_zero hb hac) (mul_ne_zero ha hbc),
    log_mul hb hac,log_mul ha hbc]
  field_simp
  ring

theorem weight_bounds : weightLower ≤ weightMass ∧ weightMass ≤ weightUpper := by
  have hl := SharpLogRecurrence.log_lower (show (1 : ℝ) ≤ ratio by norm_num [ratio,a,b])
  have hu := JointLogTotalComparison.log_le_V (show (1 : ℝ) ≤ ratio by norm_num [ratio,a,b])
  dsimp [weightLower,weightMass,weightUpper,b]
  constructor <;> linarith only [hl,hu]

theorem weightLower_pos : 0 < weightLower := by
  norm_num [weightLower,ratio,a,b,lowerLog]

theorem endpoint_log_bounds {t : ℝ} (ht : t ∈ Icc a b) :
    lowerLog (2-3*b) ≤ log (2-3*t) ∧ log (2-3*t) ≤ V (2-3*a) := by
  have hl := SharpLogRecurrence.log_lower (show (1 : ℝ) ≤ 2-3*b by norm_num [b])
  have hu := JointLogTotalComparison.log_le_V (show (1 : ℝ) ≤ 2-3*a by norm_num [a])
  have hp : 0 < 2-3*b := by norm_num [b]
  have ht0 : 0 < 2-3*t := hp.trans_le (by linarith [ht.2])
  exact ⟨hl.trans (Real.log_le_log hp (by linarith [ht.2])),
    (Real.log_le_log ht0 (by linarith [ht.1])).trans hu⟩

theorem exact_weight_gain_bounds :
    gainLower ≤ 2*(U8CanonicalMother.L-U8CanonicalMother.I) ∧
    2*(U8CanonicalMother.L-U8CanonicalMother.I) ≤ gainUpper := by
  have hl := intervalIntegral.integral_mono_on a_lt_b.le
    (weight_integrable.const_mul (lowerLog (2-3*b)))
    OriginalU8.SymbolicSmallGain.gain_integrable (fun t ht => by
      calc
        lowerLog (2-3*b)*weight t = weight t*lowerLog (2-3*b) := mul_comm _ _
        _ ≤ weight t*log (2-3*t) :=
          mul_le_mul_of_nonneg_left (endpoint_log_bounds ht).1 (weight_nonneg ht)
        _ = (b-t)*log (2-3*t)/(t*(1-t)^2) := by unfold weight; ring)
  have hu := intervalIntegral.integral_mono_on a_lt_b.le
    OriginalU8.SymbolicSmallGain.gain_integrable
    (weight_integrable.const_mul (V (2-3*a))) (fun t ht => by
      calc
        (b-t)*log (2-3*t)/(t*(1-t)^2) = weight t*log (2-3*t) := by
          unfold weight; ring
        _ ≤ weight t*V (2-3*a) :=
          mul_le_mul_of_nonneg_left (endpoint_log_bounds ht).2 (weight_nonneg ht)
        _ = V (2-3*a)*weight t := mul_comm _ _)
  rw [intervalIntegral.integral_const_mul,weight_integral] at hl hu
  have hl0 : 0 ≤ lowerLog (2-3*b) := by norm_num [lowerLog,b]
  have hu0 : 0 ≤ V (2-3*a) := by norm_num [V,upperLog,lowerLog,a]
  have hwl := mul_le_mul_of_nonneg_left weight_bounds.1 hl0
  have hwu := mul_le_mul_of_nonneg_left weight_bounds.2 hu0
  change gainLower ≤ 2*(OriginalU8.SymbolicSmallGain.L-OriginalU8.Weighted.originalSmallIntegral) ∧
    2*(OriginalU8.SymbolicSmallGain.L-OriginalU8.Weighted.originalSmallIntegral) ≤ gainUpper
  rw [OriginalU8.SymbolicSmallGain.gain_identity]
  unfold gainLower gainUpper
  constructor <;> linarith only [hl,hu,hwl,hwu]

/-- This is a strict improvement of the prior certificate, not a target claim. -/
theorem gain_strictly_tighter :
    (70/17 : ℝ)*(b-a)^2 < gainLower := by
  norm_num [gainLower,weightLower,ratio,a,b,lowerLog]

/-- The sixth correction is present once and only once. -/
theorem actual_identity : U8CanonicalMother.improvedCoefficient =
    JointHMotherPayment.unroundedCoefficient +
      (FullAdmissibleSeed.Gamma6-47/481250)/4 +
      2*(U8CanonicalMother.L-U8CanonicalMother.I) := by
  rw [U8CanonicalMother.improvedCoefficient,U8CanonicalMother.Q,
    FullAdmissibleCount.Qnew_identity]

def lowerCoefficient : ℝ := GlobalLogRelationPayment.lowerRational+
  (FullAdmissibleStrength.polynomialPayment-47/481250)/4+gainLower

theorem actual_lower : lowerCoefficient < U8CanonicalMother.improvedCoefficient := by
  have ho := GlobalLogRelationPayment.actual_lower
  have hs := FullAdmissibleStrength.polynomial_payment
  have hg := exact_weight_gain_bounds.1
  rw [actual_identity]
  unfold lowerCoefficient
  linarith only [ho,hs,hg]

/-- The residual is retained exactly, without rounding the signed log packet. -/
def residual : ℝ := GlobalLogRelationPayment.lowerRemainder-
  (FullAdmissibleStrength.polynomialPayment-47/481250)/4-gainLower

theorem residual_identity : residual =
    8*V (5000/4469)-lowerCoefficient := by
  unfold residual lowerCoefficient GlobalLogRelationPayment.lowerRemainder
  ring

theorem actual_target_residual :
    8*log (5000/4469)-U8CanonicalMother.improvedCoefficient < residual := by
  have ht := JointLogTotalComparison.log_le_V (show (1 : ℝ) ≤ 5000/4469 by norm_num)
  have hl := actual_lower
  rw [residual_identity]
  linarith only [ht,hl]

/-- A symbolic upper on the actual coefficient retains Gamma6, not a fake cap. -/
theorem actual_upper_retaining_gamma : U8CanonicalMother.improvedCoefficient <
    FifthReciprocalAffineUpper.upperRational+
      (FullAdmissibleSeed.Gamma6-47/481250)/4+gainUpper := by
  have ho := FifthReciprocalAffineUpper.actual_upper
  have hg := exact_weight_gain_bounds.2
  rw [actual_identity]
  linarith only [ho,hg]

/-- Literal ordinary-P2 consequence of the sharper coefficient lower bound. -/
theorem sharper_ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (lowerCoefficient-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := U8CanonicalMother.improved_ordinary_P2 η hη
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right actual_lower.le η) hs).trans (h N hN he)

/-- Exact fixed-rational arithmetic; no numerical evaluation of log or integrals. -/
theorem gainLower_exact : gainLower =
    118807398821384/25822353100838967 := by
  norm_num [gainLower,weightLower,ratio,a,b,lowerLog]

theorem gainLower_bounds : (4600/1000000 : ℝ) < gainLower ∧
    gainLower < 4601/1000000 := by
  rw [gainLower_exact]
  norm_num

theorem coefficient_certificate_bounds : (827883/1000000 : ℝ) < lowerCoefficient ∧
    lowerCoefficient < 827884/1000000 := by
  unfold lowerCoefficient
  rw [GlobalLogRelationPayment.lower_rational_exact,
    FullAdmissibleStrength.polynomial_payment_exact,gainLower_exact]
  norm_num

theorem residual_bounds : (70302/1000000 : ℝ) < residual ∧
    residual < 70303/1000000 := by
  unfold residual
  rw [GlobalLogRelationPayment.lower_remainder_exact,
    FullAdmissibleStrength.polynomial_payment_exact,gainLower_exact]
  norm_num

/-- Failure of this lower certificate to cross the target is not failure of actual Q. -/
theorem certificate_below_target : lowerCoefficient < 8*log (5000/4469) := by
  have hl := SharpLogRecurrence.log_lower (show (1 : ℝ) ≤ 5000/4469 by norm_num)
  have hc : (827884/1000000 : ℝ) < 8*lowerLog (5000/4469) := by norm_num [lowerLog]
  exact coefficient_certificate_bounds.2.trans (hc.trans_le (by linarith only [hl]))

/-- Precisely the remaining mathematical comparison; neither direction is asserted. -/
theorem target_iff_old_gap :
    8*log (5000/4469) < U8CanonicalMother.improvedCoefficient ↔
    8*log (5000/4469)-JointHMotherPayment.unroundedCoefficient <
      (FullAdmissibleSeed.Gamma6-47/481250)/4+
      2*(U8CanonicalMother.L-U8CanonicalMother.I) := by
  rw [actual_identity]
  constructor <;> intro h <;> linarith only [h]

/-- A strict, eta-free ordinary-P2 lower bound, still below the requested target. -/
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

end U8ActualThreshold
