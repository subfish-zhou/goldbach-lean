import MathlibNt.SieveTheory.LiLiuGoldbachLogDarboux
import MathlibNt.SieveTheory.LiLiuGoldbachPairIdealCoordinate

open MeasureTheory Set
open scoped NNReal Interval
open MathlibNt.SieveTheory
open JurkatRichert1965ChenGammaOneQOne
open LiLiuPrereqWF.CoordinateShift
open LiLiuOnePlusOneNine.GoldbachBig
open LiuWeight PrimeReciprocalLogRectangle

noncomputable section
namespace LiLiuGoldbachIdealPairKernel

/-- The actual JR lower kernel, with arbitrary real truncation parameter. -/
def kernel (τ : ℝ) (x : ℝ × ℝ) : ℝ :=
  max 0 (jr1965f ((1/2 - x.1 - x.2)/(4/53 : ℝ)) - τ)

/-- A uniform constant for the product sup metric; independent of truncation. -/
def kernelLipschitzConstant : ℝ≥0 :=
  ⟨jr1965DelayConstant / (4/53 : ℝ), div_nonneg delayConstant_pos.le (by norm_num)⟩

theorem kernel_nonneg (τ : ℝ) (x : ℝ × ℝ) : 0 ≤ kernel τ x := le_max_left _ _

theorem kernel_lipschitz (τ : ℝ) : LipschitzWith kernelLipschitzConstant (kernel τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : |x.1-y.1| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hy : |x.2-y.2| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hcoord : |(1/2-x.1-x.2)/(4/53 : ℝ) - (1/2-y.1-y.2)/(4/53 : ℝ)| ≤
      (2/(4/53 : ℝ)) * dist x y := by
    have he : (1/2-x.1-x.2)/(4/53 : ℝ) - (1/2-y.1-y.2)/(4/53 : ℝ) =
        -((x.1-y.1)+(x.2-y.2))/(4/53 : ℝ) := by ring
    rw [he, abs_div, abs_neg]
    norm_num
    have h := abs_add_le (x.1-y.1) (x.2-y.2)
    nlinarith
  have hclip := abs_max_sub_max_le_abs
    (jr1965f ((1/2-x.1-x.2)/(4/53 : ℝ))-τ)
    (jr1965f ((1/2-y.1-y.2)/(4/53 : ℝ))-τ) 0
  rw [max_comm _ 0, max_comm _ 0, sub_sub_sub_cancel_right] at hclip
  rw [Real.dist_eq]
  calc
    |kernel τ x - kernel τ y| ≤
        |jr1965f ((1/2-x.1-x.2)/(4/53 : ℝ)) - jr1965f ((1/2-y.1-y.2)/(4/53 : ℝ))| := hclip
    _ ≤ jr1965DelayConstant/2 *
        |(1/2-x.1-x.2)/(4/53 : ℝ) - (1/2-y.1-y.2)/(4/53 : ℝ)| :=
      LiLiuGoldbachJRLowerLipschitz.lower_abs_sub_le _ _
    _ ≤ jr1965DelayConstant/2 * ((2/(4/53 : ℝ))*dist x y) :=
      mul_le_mul_of_nonneg_left hcoord (div_nonneg delayConstant_pos.le (by norm_num))
    _ = (kernelLipschitzConstant : ℝ) * dist x y := by
      change jr1965DelayConstant/2 * ((2/(4/53 : ℝ))*dist x y) =
        (jr1965DelayConstant/(4/53 : ℝ))*dist x y
      ring

/-- Multiplicative logarithmic coordinates, also when log N is zero. -/
theorem primeLogExponent_mul (N : ℕ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    primeLogExponent N (r*s) = primeLogExponent N r + primeLogExponent N s := by
  unfold primeLogExponent
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hr.ne') (by exact_mod_cast hs.ne'), add_div]

/-- Exact genuine totient weight, with no primality or distinctness assumption. -/
theorem kernel_div_totient_eq (N : ℕ) (τ : ℝ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    kernel τ (primeLogExponent N r, primeLogExponent N s) / (Nat.totient (r*s) : ℝ) =
      goldbachPairIdealWeight N τ (r*s) := by
  unfold kernel goldbachPairIdealWeight
  change max 0 (jr1965f ((1/2-primeLogExponent N r-primeLogExponent N s)/(4/53 : ℝ))-τ) / _ =
    max 0 (jr1965f ((1/2-primeLogExponent N (r*s))/(4/53 : ℝ))-τ) / _
  rw [primeLogExponent_mul N hr hs, sub_add_eq_sub_sub]

/-- The raw reciprocal-product term is dominated by the genuine totient weight. -/
theorem kernel_div_product_le (N : ℕ) (τ : ℝ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    kernel τ (primeLogExponent N r, primeLogExponent N s) / ((r:ℝ)*s) ≤
      goldbachPairIdealWeight N τ (r*s) := by
  rw [← kernel_div_totient_eq N τ hr hs]
  apply div_le_div_of_nonneg_left (kernel_nonneg _ _)
  · exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hr hs)
  · exact_mod_cast Nat.totient_le (r*s)

/-- The diagonal retains totient of the square, not a product of totients. -/
theorem kernel_div_totient_square_eq (N : ℕ) (τ : ℝ) {r : ℕ} (hr : 0 < r) :
    kernel τ (primeLogExponent N r, primeLogExponent N r) / (Nat.totient (r^2) : ℝ) =
      goldbachPairIdealWeight N τ (r^2) := by
  simpa only [pow_two] using kernel_div_totient_eq N τ hr hr

/-- Pointwise truncation loses at most its nonnegative parameter. -/
theorem kernel_truncation_loss {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ × ℝ) :
    kernel 0 x - τ ≤ kernel τ x := by
  unfold kernel
  simp only [sub_zero]
  rcases le_total (jr1965f ((1/2-x.1-x.2)/(4/53 : ℝ))) 0 with h | h
  · rw [max_eq_left h]
    exact le_trans (by linarith) (le_max_left _ _)
  · rw [max_eq_right h]
    exact le_max_right _ _

/-- Weighted integrability is automatic on every positive rectangle. -/
theorem kernel_weighted_integrable (τ : ℝ) {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun x => kernel τ x / (x.1*x.2)) (Ioc a b ×ˢ Ioc c d) :=
  LiLiuGoldbachLogDarboux.weighted_integrable ha hc (kernel_lipschitz τ).continuous

/-- Explicit truncation loss for the actual JR kernel on a positive rectangle. -/
theorem integral_truncation_loss {a b c d τ : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hcd : c < d) (hτ : 0 ≤ τ) :
    (∫ u in a..b, ∫ v in c..d, kernel 0 (u,v)/(u*v)) -
      τ * logarithmicRectangleMass a b c d ≤
    ∫ u in a..b, ∫ v in c..d, kernel τ (u,v)/(u*v) := by
  have hki := kernel_weighted_integrable 0 (b := b) (d := d) ha hc
  have hti := kernel_weighted_integrable τ (b := b) (d := d) ha hc
  have hdi := LiLiuGoldbachLogDarboux.weighted_integrable (b := b) (d := d) ha hc
    (continuous_const : Continuous (fun _ : ℝ × ℝ => (1:ℝ)))
  have hfi := LiLiuGoldbachLogDarboux.weighted_integrable (b := b) (d := d) ha hc
    ((kernel_lipschitz 0).continuous.sub continuous_const : Continuous (fun x => kernel 0 x - τ))
  have heq : (∫ x in Ioc a b ×ˢ Ioc c d, (kernel 0 x-τ)/(x.1*x.2)) =
      (∫ u in a..b, ∫ v in c..d, kernel 0 (u,v)/(u*v)) -
        τ * logarithmicRectangleMass a b c d := by
    simp_rw [sub_div, div_eq_mul_one_div τ]
    have hid : (∫ x in Ioc a b ×ˢ Ioc c d, 1/(x.1*x.2)) =
        logarithmicRectangleMass a b c d :=
      (logarithmicRectangleMass_eq_setIntegral ha hab hc hcd).symm
    rw [integral_sub hki (hdi.const_mul τ), integral_const_mul, hid,
      LiLiuGoldbachLogDarboux.integral_eq_iterated hab.le hcd.le hki]
  rw [← heq, ← LiLiuGoldbachLogDarboux.integral_eq_iterated hab.le hcd.le hti]
  apply setIntegral_mono_on hfi hti (measurableSet_Ioc.prod measurableSet_Ioc)
  intro x hx
  exact div_le_div_of_nonneg_right (kernel_truncation_loss hτ x)
    (mul_pos (ha.trans hx.1.1) (hc.trans hx.2.1)).le

end LiLiuGoldbachIdealPairKernel
