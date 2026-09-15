import E09JointMainMajorLog

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.E09JointMainMajor
open FixedCoefficientUpperEnclosure (a)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)

def polePolynomial : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, q, x => x ^ (n + 1) / (n + 1 : ℕ) - q * polePolynomial n q x

def polePrimitive (n : ℕ) (q x : ℝ) : ℝ :=
  (-q) ^ n * log (q + x) + polePolynomial n q x

theorem polePrimitive_zero (q x : ℝ) : polePrimitive 0 q x = log (q + x) := by
  simp [polePrimitive, polePolynomial]

theorem polePrimitive_succ (n : ℕ) (q x : ℝ) :
    polePrimitive (n + 1) q x =
      x ^ (n + 1) / (n + 1 : ℕ) - q * polePrimitive n q x := by
  simp only [polePrimitive, polePolynomial, pow_succ]
  ring

theorem polePrimitive_derivative (n : ℕ) (q x : ℝ) (hx : q + x ≠ 0) :
    HasDerivAt (polePrimitive n q) (x ^ n / (q + x)) x := by
  induction n with
  | zero =>
    rw [show polePrimitive 0 q = fun x => log (q + x) from funext (polePrimitive_zero q)]
    simpa using
      (((hasDerivAt_id x).const_add q).log hx)
  | succ n ih =>
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfun : polePrimitive (n + 1) q =
        fun x => x ^ (n + 1) / (n + 1 : ℕ) - q * polePrimitive n q x := by
      funext x
      exact polePrimitive_succ n q x
    rw [hfun]
    have hp := ((hasDerivAt_id x).pow (n + 1)).div_const ((n + 1 : ℕ) : ℝ)
    convert! hp.sub (ih.const_mul q) using 1
    simp only [Nat.add_sub_cancel, id_eq, mul_one]
    field_simp [hx, hn]
    rw [pow_succ]
    ring

def middleCoordinate (t : ℝ) : ℝ := 5 - u t
def middlePole : ℝ := c 5 / a

def weightedMonomialPrimitive (n : ℕ) (t : ℝ) : ℝ :=
  16 * polePrimitive n middlePole (middleCoordinate t) +
    8 * polePrimitive n (-5) (middleCoordinate t)

theorem weightedMonomial_derivative (n : ℕ) {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    HasDerivAt (weightedMonomialPrimitive n)
      (SharedRationalEnvelope.weight t * middleCoordinate t ^ n) t := by
  have hg := JointSharedTightEnclosure.middle_geometry ht
  have hq : middlePole + middleCoordinate t ≠ 0 := by
    have he : middlePole + middleCoordinate t = t / a := by
      unfold middlePole middleCoordinate c u
      field_simp [truncatedSixthLower_parameters.1.ne']
      ring
    rw [he]
    exact div_ne_zero hg.1.ne' truncatedSixthLower_parameters.1.ne'
  have hm : -5 + middleCoordinate t ≠ 0 := by
    unfold middleCoordinate
    linarith [hg.2.2.1]
  have hd : HasDerivAt middleCoordinate (1 / a) t := by
    convert! (hasDerivAt_const t (5 : ℝ)).sub
      (((hasDerivAt_const t (1 / 2 : ℝ)).sub (hasDerivAt_id t)).div_const a) using 1
    ring
  convert! (((polePrimitive_derivative n middlePole (middleCoordinate t) hq).comp t hd).const_mul 16).add
    (((polePrimitive_derivative n (-5) (middleCoordinate t) hm).comp t hd).const_mul 8) using 1
  have he : SharedRationalEnvelope.weight t =
      16 / (middlePole + middleCoordinate t) / a +
        8 / (-5 + middleCoordinate t) / a := by
    have hta : middlePole + middleCoordinate t = t / a := by
      unfold middlePole middleCoordinate c u
      field_simp [truncatedSixthLower_parameters.1.ne']
      ring
    have htb : -5 + middleCoordinate t = -(1 / 2 - t) / a := by
      unfold middleCoordinate u
      ring
    rw [hta, htb]
    unfold SharedRationalEnvelope.weight
    have htwo : 1 - t * 2 ≠ 0 := by linarith [hg.2.1]
    field_simp [truncatedSixthLower_parameters.1.ne', hg.1.ne', hg.2.1.ne', htwo]
    ring
  rw [he]
  ring

def monomialEndpoint (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  16 * ((-middlePole) ^ n * f (527 / 327) +
    polePolynomial n middlePole 1 - polePolynomial n middlePole 0) +
  8 * (-(5 : ℝ) ^ n * f (5 / 4) +
    polePolynomial n (-5) 1 - polePolynomial n (-5) 0)

theorem weightedMonomial_ftc (n : ℕ) :
    (∫ t in c 5..c 4, SharedRationalEnvelope.weight t * middleCoordinate t ^ n) =
      monomialEndpoint n log := by
  have ho : c 5 ≤ c 4 := by norm_num [c, a, truncatedSixthLowerAlpha]
  have hi := JointSharedTightEnclosure.weighted_integrable (fun v => (5 - v) ^ n)
    (by fun_prop) (by norm_num [c, a, truncatedSixthLowerAlpha])
    SharedRationalEnvelope.window_order.2.1 ho
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => weightedMonomial_derivative n (uIcc_of_le ho ▸ ht)) hi]
  have h0 : middleCoordinate (c 5) = 0 := by
    norm_num [middleCoordinate, u, c, a, truncatedSixthLowerAlpha]
  have h1 : middleCoordinate (c 4) = 1 := by
    norm_num [middleCoordinate, u, c, a, truncatedSixthLowerAlpha]
  have he : log (middlePole + 1) - log (middlePole + 0) = log (527 / 327 : ℝ) := by
    rw [← log_div (by norm_num [middlePole, c, a, truncatedSixthLowerAlpha])
      (by norm_num [middlePole, c, a, truncatedSixthLowerAlpha])]
    norm_num [middlePole, c, a, truncatedSixthLowerAlpha]
  have hf : log (-5 + 1 : ℝ) - log (-5 + 0 : ℝ) = -log (5 / 4 : ℝ) := by
    norm_num only
    rw [log_neg_eq_log, log_neg_eq_log,
      log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  unfold weightedMonomialPrimitive
  rw [h0, h1]
  unfold polePrimitive monomialEndpoint
  have he5 : -(-5 : ℝ) = 5 := by norm_num
  rw [he5]
  rw [sub_eq_iff_eq_add.mp he, sub_eq_iff_eq_add.mp hf]
  ring

end WuTarget.E09JointMainMajor
