import E09JointMainMajorHigh

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval BigOperators

namespace WuTarget.E09JointMainMajor
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)

theorem weightedMonomial_high_derivative (n : ℕ) {t : ℝ} (ht : t ∈ Icc a (c 5)) :
    HasDerivAt (weightedMonomialPrimitive n)
      (SharedRationalEnvelope.weight t * middleCoordinate t ^ n) t := by
  have hg := HighSharedKernelMagnitude.high_geometry ht
  have hta : middlePole + middleCoordinate t = t / a := by
    unfold middlePole middleCoordinate c u
    field_simp [truncatedSixthLower_parameters.1.ne']
    ring
  have htb : -5 + middleCoordinate t = -(1 / 2 - t) / a := by
    unfold middleCoordinate u
    ring
  have hq : middlePole + middleCoordinate t ≠ 0 := by
    rw [hta]
    exact div_ne_zero hg.1.ne' truncatedSixthLower_parameters.1.ne'
  have hm : -5 + middleCoordinate t ≠ 0 := by
    rw [htb]
    exact div_ne_zero (neg_ne_zero.mpr hg.2.1.ne') truncatedSixthLower_parameters.1.ne'
  have hd : HasDerivAt middleCoordinate (1 / a) t := by
    convert! (hasDerivAt_const t (5 : ℝ)).sub
      (((hasDerivAt_const t (1 / 2 : ℝ)).sub (hasDerivAt_id t)).div_const a) using 1
    ring
  convert! (((polePrimitive_derivative n middlePole (middleCoordinate t) hq).comp t hd).const_mul 16).add
    (((polePrimitive_derivative n (-5) (middleCoordinate t) hm).comp t hd).const_mul 8) using 1
  have he : SharedRationalEnvelope.weight t =
      16 / (middlePole + middleCoordinate t) / a +
        8 / (-5 + middleCoordinate t) / a := by
    rw [hta, htb]
    unfold SharedRationalEnvelope.weight
    have htwo : 1 - t * 2 ≠ 0 := by linarith [hg.2.1]
    field_simp [truncatedSixthLower_parameters.1.ne', hg.1.ne', hg.2.1.ne', htwo]
    ring
  rw [he]
  ring

def highMonomialEndpoint (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  16 * ((-middlePole) ^ n * f (327 / 200) +
    polePolynomial n middlePole 0 - polePolynomial n middlePole (-127 / 200)) +
  8 * (-(5 : ℝ) ^ n * f (1127 / 1000) +
    polePolynomial n (-5) 0 - polePolynomial n (-5) (-127 / 200))

theorem weightedMonomial_high_ftc (n : ℕ) :
    (∫ t in a..c 5, SharedRationalEnvelope.weight t * middleCoordinate t ^ n) =
      highMonomialEndpoint n log := by
  have ho : a ≤ c 5 := by norm_num [c, a, truncatedSixthLowerAlpha]
  have hi := JointSharedTightEnclosure.weighted_integrable (l := a) (r := c 5)
    (fun v => (5 - v) ^ n) (by fun_prop) le_rfl
    (by norm_num [c, a, s, truncatedSixthLowerAlpha, truncatedSixthLowerSigma]) ho
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => weightedMonomial_high_derivative n (uIcc_of_le ho ▸ ht)) hi]
  have h0 : middleCoordinate (c 5) = 0 := by
    norm_num [middleCoordinate, u, c, a, truncatedSixthLowerAlpha]
  have h1 : middleCoordinate a = -127 / 200 := by
    norm_num [middleCoordinate, u, a, truncatedSixthLowerAlpha]
  have he : log (middlePole + 0) - log (middlePole + (-127 / 200)) =
      log (327 / 200 : ℝ) := by
    norm_num [middlePole, c, a, truncatedSixthLowerAlpha]
  have hf : log (-5 + 0 : ℝ) - log (-5 + (-127 / 200) : ℝ) =
      -log (1127 / 1000 : ℝ) := by
    have hlog := log_div (by norm_num : (1127 / 200 : ℝ) ≠ 0)
      (by norm_num : (5 : ℝ) ≠ 0)
    norm_num at hlog ⊢
    linarith only [hlog]
  unfold weightedMonomialPrimitive
  rw [h0, h1]
  unfold polePrimitive highMonomialEndpoint
  rw [show -(-5 : ℝ) = 5 by norm_num,
    sub_eq_iff_eq_add.mp he, sub_eq_iff_eq_add.mp hf]
  ring

def highCoefficients : Fin 5 → ℝ :=
  ![9044059 / 6431250 - upperFive,
    highA0 - (9044059 / 6431250) / 5,
    -highA1 / 2, highA2 / 3, -highA3 / 4]

theorem high_polynomial (t : ℝ) :
    highSurplus (u t) = ∑ i : Fin 5, highCoefficients i * middleCoordinate t ^ i.val := by
  norm_num [Fin.sum_univ_succ, highCoefficients, middleCoordinate, highSurplus, highIncrement]
  ring

theorem highGain_ftc :
    highGain = ∑ i : Fin 5, highCoefficients i * highMonomialEndpoint i.val log := by
  unfold highGain
  simp_rw [high_polynomial, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [← mul_assoc, mul_comm (SharedRationalEnvelope.weight _) (highCoefficients _),
      mul_assoc, intervalIntegral.integral_const_mul, weightedMonomial_high_ftc]
  intro i hi
  have hp := JointSharedTightEnclosure.weighted_integrable
    (l := a) (r := c 5) (fun v => (5 - v) ^ i.val) (by fun_prop) le_rfl
    (by norm_num [c, a, s, truncatedSixthLowerAlpha, truncatedSixthLowerSigma])
    (by norm_num [a, c, truncatedSixthLowerAlpha])
  convert hp.const_mul (highCoefficients i) using 1
  funext t
  unfold middleCoordinate
  ring

def highLogA : ℝ := ∑ i : Fin 5, 16 * highCoefficients i * (-middlePole) ^ i.val
def highLogB : ℝ := ∑ i : Fin 5, -8 * highCoefficients i * (5 : ℝ) ^ i.val
def highRational : ℝ := ∑ i : Fin 5, highCoefficients i *
  (16 * (polePolynomial i.val middlePole 0 - polePolynomial i.val middlePole (-127 / 200)) +
    8 * (polePolynomial i.val (-5) 0 - polePolynomial i.val (-5) (-127 / 200)))

theorem high_collection (f : ℝ → ℝ) :
    (∑ i : Fin 5, highCoefficients i * highMonomialEndpoint i.val f) =
      highRational + highLogA * f (327 / 200) + highLogB * f (1127 / 1000) := by
  unfold highMonomialEndpoint highRational highLogA highLogB
  simp only [Fin.sum_univ_succ]
  ring

def highPayment : ℝ :=
  highRational + signedLog highLogA (327 / 200) + signedLog highLogB (1127 / 1000)

theorem highPayment_le_gain : highPayment ≤ highGain := by
  rw [highGain_ftc, high_collection]
  have h1 := signedLog_le highLogA (by norm_num : (1 : ℝ) ≤ 327 / 200)
  have h2 := signedLog_le highLogB (by norm_num : (1 : ℝ) ≤ 1127 / 1000)
  unfold highPayment
  linarith only [h1, h2]

theorem highPayment_pos : 0 < highPayment := by
  norm_num [highPayment, signedLog, highRational, highLogA, highLogB, highCoefficients,
    Fin.sum_univ_succ, polePolynomial, middlePole, c, a, truncatedSixthLowerAlpha,
    upperFive, highA0, highA1, highA2, highA3, logThreeCap, upperLog, lowerLog]

end WuTarget.E09JointMainMajor
