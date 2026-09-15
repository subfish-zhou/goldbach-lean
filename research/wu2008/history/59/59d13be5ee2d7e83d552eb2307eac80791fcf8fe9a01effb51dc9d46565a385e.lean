import E09JointMainMajorMiddle
import E09JointMainMajorPrimitive

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval BigOperators

namespace WuTarget.E09JointMainMajor
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)

def middleCoefficients : Fin 7 → ℝ :=
  ![9044059 / 6431250 - upperFive,
    287 / 250 - upperFour - (9044059 / 6431250 - upperFive) +
      curvaturePrimitive 1 - 1 / 144,
    1 / 144 - (7 / 480) / 2,
    -(7 / 960 + 1 / 36) / 6,
    -(7 / 2560 + 1 / 72 + 5 / 864) / 12,
    -(1 / 192 + 5 / 1728) / 20,
    -(5 / 4608) / 30]

theorem middle_polynomial (t : ℝ) :
    middleSurplus (u t) = ∑ i : Fin 7, middleCoefficients i * middleCoordinate t ^ i.val := by
  norm_num [Fin.sum_univ_succ, middleCoefficients, middleCoordinate,
    middleSurplus, chordDefect, curvaturePrimitive]
  ring

theorem middleGain_ftc :
    middleGain = ∑ i : Fin 7, middleCoefficients i * monomialEndpoint i.val log := by
  unfold middleGain
  simp_rw [middle_polynomial, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [← mul_assoc, mul_comm (SharedRationalEnvelope.weight _) (middleCoefficients _),
      mul_assoc, intervalIntegral.integral_const_mul, weightedMonomial_ftc]
  intro i hi
  have hp := JointSharedTightEnclosure.weighted_integrable
    (fun v => (5 - v) ^ i.val) (by fun_prop)
    (by norm_num [a, c, truncatedSixthLowerAlpha])
    SharedRationalEnvelope.window_order.2.1
    (by norm_num [a, c, truncatedSixthLowerAlpha])
  convert hp.const_mul (middleCoefficients i) using 1
  funext t
  unfold middleCoordinate
  ring

def middleLogA : ℝ := ∑ i : Fin 7, 16 * middleCoefficients i * (-middlePole) ^ i.val
def middleLogB : ℝ := ∑ i : Fin 7, -8 * middleCoefficients i * (5 : ℝ) ^ i.val
def middleRational : ℝ := ∑ i : Fin 7, middleCoefficients i *
  (16 * (polePolynomial i.val middlePole 1 - polePolynomial i.val middlePole 0) +
    8 * (polePolynomial i.val (-5) 1 - polePolynomial i.val (-5) 0))

theorem middle_collection (f : ℝ → ℝ) :
    (∑ i : Fin 7, middleCoefficients i * monomialEndpoint i.val f) =
      middleRational + middleLogA * f (527 / 327) + middleLogB * f (5 / 4) := by
  unfold monomialEndpoint middleRational middleLogA middleLogB
  simp only [Fin.sum_univ_succ]
  ring

theorem middle_log_signs : middleLogA ≤ 0 ∧ 0 ≤ middleLogB := by
  norm_num [middleLogA, middleLogB, Fin.sum_univ_succ, middleCoefficients,
    curvaturePrimitive, middlePole, c, a, truncatedSixthLowerAlpha,
    upperFour, upperFive, upperLog, lowerLog]

def middlePayment : ℝ :=
  middleRational + middleLogA * upperLog (527 / 327) + middleLogB * lowerLog (5 / 4)

theorem middlePayment_le_gain : middlePayment ≤ middleGain := by
  rw [middleGain_ftc, middle_collection]
  have h1 := mul_le_mul_of_nonpos_left
    (log_upper (by norm_num : (1 : ℝ) ≤ 527 / 327)) middle_log_signs.1
  have h2 := mul_le_mul_of_nonneg_left
    (log_lower (by norm_num : (1 : ℝ) ≤ 5 / 4)) middle_log_signs.2
  unfold middlePayment
  linarith only [h1, h2]

theorem middlePayment_pos : 0 < middlePayment := by
  norm_num [middlePayment, middleRational, middleLogA, middleLogB,
    Fin.sum_univ_succ, middleCoefficients, polePolynomial, middlePole,
    curvaturePrimitive, c, a, truncatedSixthLowerAlpha, upperFour, upperFive, lowerLog, upperLog]

end WuTarget.E09JointMainMajor
