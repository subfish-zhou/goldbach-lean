import MathlibNt.SieveTheory.Liu.Weights.LiuWeightPaperQ
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A genuine logarithmic-integral model for Liu's main term

For every additive normalization `κ`, this module defines
`κ + ∫ t in 2..x, 1 / log t`.  A standard paper logarithmic integral restricted
to `x ≥ 2` has this form for a particular value of `κ`.  Liu's source notation
does not identify that normalization, so it remains a parameter here.

This function is not identified with the analytic-number-theory compatibility
function called `logarithmicIntegral`, which is the historical proxy `x / log x`.
-/

open MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.LiuWeight

/-- The logarithmic integral above `2`, with an explicit additive normalization. -/
noncomputable def liuLogarithmicIntegral (κ x : ℝ) : ℝ :=
  κ + ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- Changing the additive normalization changes the logarithmic integral by
exactly the same constant. -/
@[simp] theorem liuLogarithmicIntegral_sub_normalization
    (κ₂ κ₁ x : ℝ) :
    liuLogarithmicIntegral κ₂ x - liuLogarithmicIntegral κ₁ x = κ₂ - κ₁ := by
  simp [liuLogarithmicIntegral]

/-- Difference between Liu's genuine logarithmic integral and the `x / log x`
proxy used in the source main-term calculation. -/
noncomputable def liuLogarithmicIntegralRemainder (κ x : ℝ) : ℝ :=
  liuLogarithmicIntegral κ x - x / Real.log x

/-- A global upper-model constant for `liuLogarithmicIntegral κ` on `x ≥ 2`. -/
noncomputable def liuLogarithmicIntegralUpperConstant (κ : ℝ) : ℝ :=
  |κ| + 2 / Real.log 2 + 2

/-- The logarithmic-integral density is nonnegative above `2`. -/
lemma liuLogarithmicIntegrand_nonneg {t : ℝ} (ht : 2 ≤ t) :
    0 ≤ 1 / Real.log t := by
  exact one_div_nonneg.mpr (le_of_lt (Real.log_pos (by linarith)))

/-- The logarithmic-integral density is interval integrable on every interval
whose left endpoint is at least `2`. -/
lemma liuLogarithmicIntegrand_intervalIntegrable_of_two_le
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
  apply intervalIntegral.intervalIntegrable_one_div
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  · apply Real.continuousOn_log.mono
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]

/-- The density is integrable from `2` to every `x ≥ 2`. -/
lemma liuLogarithmicIntegrand_intervalIntegrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x :=
  liuLogarithmicIntegrand_intervalIntegrable_of_two_le (le_refl 2) hx

/-- The logarithmic integral from `2` to `x ≥ 2` is nonnegative. -/
lemma liuLogarithmicIntegral_integral_nonneg {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t := by
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  exact liuLogarithmicIntegrand_nonneg ht.1

/-- A nonnegative additive normalization makes the genuine logarithmic integral
nonnegative throughout its source range. -/
lemma liuLogarithmicIntegral_nonneg (κ : ℝ) (hκ : 0 ≤ κ)
    {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ liuLogarithmicIntegral κ x := by
  unfold liuLogarithmicIntegral
  exact add_nonneg hκ (liuLogarithmicIntegral_integral_nonneg hx)

/-- The squared logarithmic density is interval integrable above `2`. -/
lemma liuLogarithmicSquaredIntegrand_intervalIntegrable
    {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x := by
  apply intervalIntegral.intervalIntegrable_one_div
  · intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  · apply (Real.continuousOn_log.mono ?_).pow 2
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]

/-- Derivative identity behind integration by parts for `x / log x`. -/
lemma hasDerivAt_div_log {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun u : ℝ => u / Real.log u)
      (1 / Real.log t - 1 / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hd := (hasDerivAt_id t).fun_div (Real.hasDerivAt_log ht0) hlog
  have heq : 1 / Real.log t - 1 / Real.log t ^ 2 =
      (1 * Real.log t - id t * t⁻¹) / Real.log t ^ 2 := by
    simp only [id_eq, one_mul]
    field_simp [ht0, hlog]
  exact heq ▸ hd

/-- Exact integration-by-parts expansion of the genuine-minus-proxy remainder. -/
theorem liuLogarithmicIntegralRemainder_eq (κ : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    liuLogarithmicIntegralRemainder κ x =
      κ - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hint₁ := liuLogarithmicIntegrand_intervalIntegrable hx
  have hint₂ := liuLogarithmicSquaredIntegrand_intervalIntegrable hx
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => u / Real.log u)
        (1 / Real.log t - 1 / Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact hasDerivAt_div_log ht.1
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hint₁.sub hint₂)
  rw [intervalIntegral.integral_sub hint₁ hint₂] at hfund
  unfold liuLogarithmicIntegralRemainder liuLogarithmicIntegral
  linarith

/-- The normalization `2 / log 2` makes the genuine logarithmic integral
dominate the elementary proxy on the full source range. -/
theorem div_log_le_liuLogarithmicIntegral {x : ℝ} (hx : 2 ≤ x) :
    x / Real.log x ≤ liuLogarithmicIntegral (2 / Real.log 2) x := by
  rw [← sub_nonneg]
  change 0 ≤ liuLogarithmicIntegralRemainder (2 / Real.log 2) x
  rw [liuLogarithmicIntegralRemainder_eq _ hx]
  simpa using intervalIntegral.integral_nonneg hx (fun t ht =>
    one_div_nonneg.mpr (sq_nonneg (Real.log t)))

/-- A simple global inequality used to absorb the short part of the integral. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 2 ≤ x) :
    Real.log x ≤ 2 * √x := by
  have hx0 : 0 ≤ x := by linarith
  have hsqrt_pos : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have h := Real.log_le_sub_one_of_pos hsqrt_pos
  rw [Real.log_sqrt hx0] at h
  linarith

/-- Above `2`, the ratio `x / log x` is at least one. -/
lemma one_le_div_log {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ x / Real.log x := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  apply (le_div_iff₀ hlogpos).2
  have hlog := Real.log_le_sub_one_of_pos hxpos
  linarith

/-- Bound the density by its value at the lower endpoint `2`. -/
private lemma liuLogarithmicIntegral_integral_le_sub_div_log_two
    {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, 1 / Real.log t) ≤ (x - 2) / Real.log 2 := by
  calc
    (∫ t in (2 : ℝ)..x, 1 / Real.log t) ≤
        ∫ _t in (2 : ℝ)..x, 1 / Real.log 2 := by
      apply intervalIntegral.integral_mono_on hx
        (liuLogarithmicIntegrand_intervalIntegrable hx) intervalIntegrable_const
      intro t ht
      exact one_div_le_one_div_of_le (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) ht.1)
    _ = (x - 2) / Real.log 2 := by
      simp [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

/-- Explicit global bound for the integral part.  For `x ≥ 4`, split at `√x`:
the first interval is bounded by `√x / log 2`, and on the second interval
`log t ≥ log x / 2`.  The range `2 ≤ x < 4` is handled directly. -/
lemma liuLogarithmicIntegral_integral_le {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, 1 / Real.log t) ≤
      (2 / Real.log 2 + 2) * (x / Real.log x) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hx4 : 4 ≤ x
  · have hx0 : 0 ≤ x := le_of_lt hxpos
    have hsqrt0 : 0 ≤ √x := Real.sqrt_nonneg x
    have hsqrt2 : 2 ≤ √x := by
      nlinarith [Real.sq_sqrt hx0]
    have hsqrtx : √x ≤ x := by
      nlinarith [Real.sq_sqrt hx0]
    have hint₁ := liuLogarithmicIntegrand_intervalIntegrable_of_two_le
      (le_refl 2) hsqrt2
    have hint₂ := liuLogarithmicIntegrand_intervalIntegrable_of_two_le
      hsqrt2 hsqrtx
    have hfirst : (∫ t in (2 : ℝ)..√x, 1 / Real.log t) ≤
        √x / Real.log 2 := by
      calc
        (∫ t in (2 : ℝ)..√x, 1 / Real.log t) ≤ (√x - 2) / Real.log 2 :=
          liuLogarithmicIntegral_integral_le_sub_div_log_two hsqrt2
        _ ≤ √x / Real.log 2 := by
          exact (div_le_div_iff_of_pos_right hlog2).2 (by linarith)
    have hsecond : (∫ t in √x..x, 1 / Real.log t) ≤
        2 * x / Real.log x := by
      calc
        (∫ t in √x..x, 1 / Real.log t) ≤
            ∫ _t in √x..x, 2 / Real.log x := by
          apply intervalIntegral.integral_mono_on hsqrtx hint₂ intervalIntegrable_const
          intro t ht
          calc
            1 / Real.log t ≤ 1 / (Real.log x / 2) := by
              apply one_div_le_one_div_of_le (div_pos hlogx (by norm_num))
              calc
                Real.log x / 2 = Real.log √x := (Real.log_sqrt hx0).symm
                _ ≤ Real.log t := Real.log_le_log (Real.sqrt_pos.2 hxpos) ht.1
            _ = 2 / Real.log x := by field_simp
        _ = (x - √x) * (2 / Real.log x) := by
          simp [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]
          ring
        _ ≤ 2 * x / Real.log x := by
          rw [show 2 * x / Real.log x = x * (2 / Real.log x) by ring]
          exact mul_le_mul_of_nonneg_right (by linarith)
            (div_nonneg (by norm_num) (le_of_lt hlogx))
    have hsqrt_bound : √x / Real.log 2 ≤
        (2 / Real.log 2) * (x / Real.log x) := by
      have hsqrt_log : √x * Real.log x ≤ 2 * x := by
        calc
          √x * Real.log x ≤ √x * (2 * √x) :=
            mul_le_mul_of_nonneg_left (log_le_two_mul_sqrt hx) hsqrt0
          _ = 2 * (√x) ^ 2 := by ring
          _ = 2 * x := by rw [Real.sq_sqrt hx0]
      have hsqrt_div : √x ≤ 2 * x / Real.log x :=
        (le_div_iff₀ hlogx).2 (by simpa [mul_comm] using hsqrt_log)
      calc
        √x / Real.log 2 ≤ (2 * x / Real.log x) / Real.log 2 :=
          (div_le_div_iff_of_pos_right hlog2).2 hsqrt_div
        _ = (2 / Real.log 2) * (x / Real.log x) := by ring
    rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
    calc
      (∫ t in (2 : ℝ)..√x, 1 / Real.log t) +
          ∫ t in √x..x, 1 / Real.log t ≤
          √x / Real.log 2 + 2 * x / Real.log x := add_le_add hfirst hsecond
      _ ≤ (2 / Real.log 2) * (x / Real.log x) +
          2 * x / Real.log x := add_le_add hsqrt_bound (le_refl _)
      _ = (2 / Real.log 2 + 2) * (x / Real.log x) := by ring
  · have hx4' : x ≤ 4 := le_of_not_ge hx4
    have hlogx_le : Real.log x ≤ 2 * Real.log 2 := by
      calc
        Real.log x ≤ Real.log 4 := Real.log_le_log hxpos hx4'
        _ = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num,
            Real.log_mul (by norm_num) (by norm_num)]
          ring
    have hrough := liuLogarithmicIntegral_integral_le_sub_div_log_two hx
    have hsmall : (x - 2) / Real.log 2 ≤ 2 * x / Real.log x := by
      apply (div_le_div_iff₀ hlog2 hlogx).2
      calc
        (x - 2) * Real.log x ≤ x * Real.log x :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hlogx)
        _ ≤ x * (2 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogx_le (le_of_lt hxpos)
        _ = (2 * x) * Real.log 2 := by ring
    calc
      (∫ t in (2 : ℝ)..x, 1 / Real.log t) ≤ 2 * x / Real.log x :=
        hrough.trans hsmall
      _ ≤ (2 / Real.log 2 + 2) * (x / Real.log x) := by
        have hratio : 0 ≤ x / Real.log x :=
          div_nonneg (le_of_lt hxpos) (le_of_lt hlogx)
        have hcoef : 2 ≤ 2 / Real.log 2 + 2 := by
          have : 0 ≤ 2 / Real.log 2 :=
            div_nonneg (by norm_num) (le_of_lt hlog2)
          linarith
        rw [show 2 * x / Real.log x = 2 * (x / Real.log x) by ring]
        exact mul_le_mul_of_nonneg_right hcoef hratio

/-- The explicit upper-model constant is nonnegative. -/
lemma liuLogarithmicIntegralUpperConstant_nonneg (κ : ℝ) :
    0 ≤ liuLogarithmicIntegralUpperConstant κ := by
  unfold liuLogarithmicIntegralUpperConstant
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- The normalized logarithmic integral has a global `x / log x` upper bound. -/
lemma liuLogarithmicIntegral_abs_le (κ : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    |liuLogarithmicIntegral κ x| ≤
      liuLogarithmicIntegralUpperConstant κ * x / Real.log x := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hκ : |κ| ≤ |κ| * (x / Real.log x) := by
    calc
      |κ| = |κ| * 1 := by ring
      _ ≤ |κ| * (x / Real.log x) :=
        mul_le_mul_of_nonneg_left (one_le_div_log hx) (abs_nonneg κ)
  have hint_nonneg := liuLogarithmicIntegral_integral_nonneg hx
  have hint := liuLogarithmicIntegral_integral_le hx
  unfold liuLogarithmicIntegral liuLogarithmicIntegralUpperConstant
  rw [show (|κ| + 2 / Real.log 2 + 2) * x / Real.log x =
      (|κ| + (2 / Real.log 2 + 2)) * (x / Real.log x) by ring]
  calc
    |κ + ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        |κ| + |∫ t in (2 : ℝ)..x, 1 / Real.log t| := abs_add_le _ _
    _ = |κ| + ∫ t in (2 : ℝ)..x, 1 / Real.log t := by
      rw [abs_of_nonneg hint_nonneg]
    _ ≤ |κ| * (x / Real.log x) +
        (2 / Real.log 2 + 2) * (x / Real.log x) := add_le_add hκ hint
    _ = (|κ| + (2 / Real.log 2 + 2)) * (x / Real.log x) := by ring

/-- Every additive normalization of the genuine integral family supplies the
upper model required by the finite Liu `R₁` argument. -/
lemma liuLogarithmicIntegral_paperLiUpperModel (κ : ℝ) :
    PaperLiUpperModel (liuLogarithmicIntegral κ)
      (liuLogarithmicIntegralUpperConstant κ) :=
  ⟨liuLogarithmicIntegralUpperConstant_nonneg κ,
    fun _x hx => liuLogarithmicIntegral_abs_le κ hx⟩

/-- The source-cutoff `R₁` endpoint instantiated with the genuine normalized
logarithmic-integral family. -/
theorem liuLogarithmicIntegral_paperQStyleSourceR1Majorant_le_log_square_cutoff
    (κ : ℝ) (N : ℕ) (ε : ℝ) (hN : 8 ≤ N) (hε : 0 ≤ ε) :
    paperQStyleSourceR1Majorant (liuLogarithmicIntegral κ) N
        (liuSourceZ10 N) (paperQSourceCutoff N ε)
        (liuSourceY3 N) (liuSourceD2 N) ≤
      15 * liuLogarithmicIntegralUpperConstant κ *
        liuSourceR1P₂ReciprocalBound *
        paperQStyleDivisorWeightLogConstant *
        (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 :=
  (liuLogarithmicIntegral_paperLiUpperModel κ).paperQStyleSourceR1Majorant_le_log_square_cutoff
    N ε hN hε

/-- Liu's `R₁` log-square endpoint with the outer divisor sum defined using the
source-facing real-cutoff modulus `liuPaperQModulus`. The weight lower cutoff is
separately fixed by `liuSourceZ10`. -/
theorem liuLogarithmicIntegral_liuPaperQSourceR1Majorant_le_log_square
    (κ : ℝ) (N : ℕ) (ε : ℝ) (hN : 8 ≤ N) (hε : 0 ≤ ε) :
    liuPaperQSourceR1Majorant (liuLogarithmicIntegral κ) N ε ≤
      15 * liuLogarithmicIntegralUpperConstant κ *
        liuSourceR1P₂ReciprocalBound *
        paperQStyleDivisorWeightLogConstant *
        (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  rw [liuPaperQSourceR1Majorant_eq_paperQStyleSourceR1Majorant]
  exact liuLogarithmicIntegral_paperQStyleSourceR1Majorant_le_log_square_cutoff
    κ N ε hN hε

end MathlibNt.SieveTheory.LiuWeight
