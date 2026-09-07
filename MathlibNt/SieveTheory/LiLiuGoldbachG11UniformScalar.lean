import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralBound

open MeasureTheory Set
open scoped Interval BigOperators
noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option maxHeartbeats 4000000

/-- Lower endpoint of the fixed 32-term odd-log expansion, evaluated exactly. -/
def g11UniformLogLower : ℝ :=
  65950865779868241286341246906292389374730392248406166651554921752248327983608712622624452911395657604020873914345906954334860 /
  139200177231575000540913611420539494385060560737387374997917880249188693846020408531067587241017041316034446547352995184835249

/-- Upper endpoint after adding the analytic tail, not a floating-point estimate. -/
def g11UniformLogUpper : ℝ :=
  65950865779868241286341246906292389374732357269754084435583521752248327983608712622624452911395657604020873914345906954334860 /
  139200177231575000540913611420539494385060560737387374997917880249188693846020408531067587241017041316034446547352995184835249

/-- The coefficient of the existing actual uniform-8 G11 estimate. -/
def g11UniformScalar : ℝ :=
  8 * (561522 / 1000000 : ℝ) * goldbachG11PrimeIntegral (fun _ => 1)

/-- Rational upward rounding at the prescribed denominator. -/
def g11UniformScalarUpper : ℝ := 10385101 / 100000000

/-- Only the unweighted kernel primitive is consumed from the imported file. -/
theorem goldbachG11PrimeIntegral_one_eq_uniform_primitives :
    goldbachG11PrimeIntegral (fun _ => 1) =
      g11AuthorPrimitive0 (4 / 33) - g11AuthorPrimitive0 (4 / 53) := by
  rw [goldbachG11PrimeIntegral_one_eq_single]
  exact g11AuthorKernel_integral (by norm_num) (by norm_num)

/-- Exact endpoint reduction; the linear logarithm coefficient is negative. -/
theorem goldbachG11PrimeIntegral_one_eq_uniform_log :
    goldbachG11PrimeIntegral (fun _ => 1) =
      15 + (53 / 8 : ℝ) * Real.log (53 / 33 : ℝ) ^ 2 -
        (139 / 4 : ℝ) * Real.log (53 / 33 : ℝ) := by
  rw [goldbachG11PrimeIntegral_one_eq_uniform_primitives]
  norm_num [g11AuthorPrimitive0]
  ring

/-- The exact lower and upper rational literals agree with the fixed analytic budget. -/
theorem g11UniformLog_endpoints_eq :
    g11UniformLogLower =
      2 * (∑ k ∈ Finset.range 32, (10 / 43 : ℝ) ^ (2 * k + 1) / (2 * k + 1)) ∧
    g11UniformLogUpper = g11UniformLogLower +
      2 * (10 / 43 : ℝ) ^ 65 / (1 - (10 / 43 : ℝ) ^ 2) := by
  norm_num [g11UniformLogLower, g11UniformLogUpper, Finset.sum_range_succ]

/-- Analytic odd-log bounds, with exactly 32 terms and no numerical oracle. -/
theorem g11UniformLog_bounds :
    g11UniformLogLower ≤ Real.log (53 / 33 : ℝ) ∧
      Real.log (53 / 33 : ℝ) ≤ g11UniformLogUpper := by
  have hl := Real.sum_range_le_log_div (x := (10 / 43 : ℝ))
    (by norm_num) (by norm_num) 32
  have hu := Real.log_div_le_sum_range_add (x := (10 / 43 : ℝ))
    (by norm_num) (by norm_num) 32
  have he := g11UniformLog_endpoints_eq
  have hr : ((1 + (10 / 43 : ℝ)) / (1 - (10 / 43 : ℝ))) = 53 / 33 := by norm_num
  rw [hr] at hl hu
  norm_num only at hl hu he
  constructor <;> linarith only [hl, hu, he.1, he.2]

/-- Separate directions: the positive square uses the upper log endpoint,
whereas the negative linear term uses the lower endpoint. The lower bound
reverses those choices. Thus there is no sign-incorrect endpoint substitution. -/
theorem g11UniformScalar_enclosure :
    8 * (561522 / 1000000 : ℝ) *
        (15 + (53 / 8 : ℝ) * g11UniformLogLower ^ 2 -
          (139 / 4 : ℝ) * g11UniformLogUpper) ≤ g11UniformScalar ∧
    g11UniformScalar ≤ 8 * (561522 / 1000000 : ℝ) *
        (15 + (53 / 8 : ℝ) * g11UniformLogUpper ^ 2 -
          (139 / 4 : ℝ) * g11UniformLogLower) := by
  obtain ⟨hl, hu⟩ := g11UniformLog_bounds
  have hs : 0 ≤ g11UniformLogLower := by norm_num [g11UniformLogLower]
  have hlog : 0 ≤ Real.log (53 / 33 : ℝ) := hs.trans hl
  have hsqlo : g11UniformLogLower ^ 2 ≤ Real.log (53 / 33 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hs hl 2
  have hsqhi : Real.log (53 / 33 : ℝ) ^ 2 ≤ g11UniformLogUpper ^ 2 :=
    pow_le_pow_left₀ hlog hu 2
  unfold g11UniformScalar
  rw [goldbachG11PrimeIntegral_one_eq_uniform_log]
  constructor <;> nlinarith only [hl, hu, hsqlo, hsqhi]

/-- Exact rational comparison of both analytic endpoints with the rounded upper. -/
theorem g11UniformScalar_rational_budget :
    8 * (561522 / 1000000 : ℝ) *
        (15 + (53 / 8 : ℝ) * g11UniformLogUpper ^ 2 -
          (139 / 4 : ℝ) * g11UniformLogLower) < g11UniformScalarUpper ∧
    g11UniformScalarUpper -
      8 * (561522 / 1000000 : ℝ) *
        (15 + (53 / 8 : ℝ) * g11UniformLogLower ^ 2 -
          (139 / 4 : ℝ) * g11UniformLogUpper) ≤ (1 / 1000000 : ℝ) := by
  norm_num [g11UniformScalarUpper, g11UniformLogLower, g11UniformLogUpper]

/-- Strictness leaves enough genuine slack to obtain a fixed numeric count bound. -/
theorem g11UniformScalar_lt_upper : g11UniformScalar < g11UniformScalarUpper :=
  g11UniformScalar_enclosure.2.trans_lt g11UniformScalar_rational_budget.1

/-- Requested one-sided error certificate for the actual uniform-8 coefficient. -/
theorem g11UniformScalar_upper_error :
    0 ≤ g11UniformScalarUpper - g11UniformScalar ∧
      g11UniformScalarUpper - g11UniformScalar ≤ (1 / 1000000 : ℝ) := by
  constructor
  · exact sub_nonneg.mpr g11UniformScalar_lt_upper.le
  · linarith only [g11UniformScalar_enclosure.1, g11UniformScalar_rational_budget.2]

/-- Literal version for consumers that do not unfold the scalar definitions. -/
theorem goldbachG11_uniform8_coefficient_error :
    0 ≤ (10385101 / 100000000 : ℝ) -
      8 * (561522 / 1000000 : ℝ) * goldbachG11PrimeIntegral (fun _ => 1) ∧
    (10385101 / 100000000 : ℝ) -
      8 * (561522 / 1000000 : ℝ) * goldbachG11PrimeIntegral (fun _ => 1) ≤
        (1 / 1000000 : ℝ) :=
  g11UniformScalar_upper_error

/-- Explicitly excludes relabeling the present coefficient as the author's 0.10191. -/
theorem goldbachG11_uniform8_coefficient_gt_author_number :
    (10191 / 100000 : ℝ) <
      8 * (561522 / 1000000 : ℝ) * goldbachG11PrimeIntegral (fun _ => 1) := by
  have h := g11UniformScalar_upper_error.2
  change g11UniformScalarUpper - g11UniformScalar ≤ (1 / 1000000 : ℝ) at h
  change (10191 / 100000 : ℝ) < g11UniformScalar
  norm_num [g11UniformScalarUpper] at h
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig