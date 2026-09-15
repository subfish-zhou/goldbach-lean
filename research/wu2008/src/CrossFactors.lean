import FreshExactBudget

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open F1BFullFTC F1SecondLogRecovery FreshRemainingFactors
open scoped Interval
namespace F1FactorCross

/-- The entire prescribed rational part of the second factor difference. -/
def rationalB (u : ℝ) : ℝ := splitL (ratio u)+kept (ratio u)-linearB u
/-- No endpoint weakening and no extra remainder order. -/
def crossA (u : ℝ) : ℝ := kept (u-1)/u*rationalB u
def crossB (u : ℝ) : ℝ := factorA u/u*kept (ratio u)
def cross (u : ℝ) : ℝ := crossA u+crossB u
/-- The original two logarithmic tails, with their exact enlarged coefficients. -/
def tails (u : ℝ) : ℝ := logTail (u-1)/u*log (ratio u)+
  (splitL (u-1)+kept (u-1))/u*logTail (ratio u)

theorem rationalB_exact (u : ℝ) : factorB u = rationalB u+logTail (ratio u) := by
  unfold factorB rationalB logTail
  ring

theorem split_linear_gap {x : ℝ} (hx : 1 ≤ x) :
    2*(x-1)/(x+3)+2*(x-1)/(3*x+1)-2*(x-1)/(x+1) =
      2*(x-1)^3/((x+3)*(3*x+1)*(x+1)) := by
  have h1 : x+3 ≠ 0 := by linarith
  have h2 : 3*x+1 ≠ 0 := by linarith
  have h3 : x+1 ≠ 0 := by linarith
  field_simp
  ring

theorem splitL_ge_linear {x : ℝ} (hx : 1 ≤ x) :
    2*(x-1)/(x+1) ≤ splitL x := by
  have h := splitL_linear (u := x+1) (by linarith)
  have hid := split_linear_gap hx
  have hp : 0 ≤ 2*(x-1)^3/((x+3)*(3*x+1)*(x+1)) := by
    have hm : 0 ≤ x-1 := by linarith
    have hx0 : 0 < x := by linarith
    positivity
  have hrewrite : 2*(x+1-2)/(x+1+2)+2*(x+1-2)/(3*(x+1)-2) =
      2*(x-1)/(x+3)+2*(x-1)/(3*x+1) := by congr 1 <;> congr 1 <;> ring
  rw [show x+1-1=x by ring,hrewrite] at h
  linarith only [h,hid,hp]

theorem linearB_ratio {u : ℝ} (hu : 2 ≤ u) :
    linearB u = 2*(ratio u-1)/(ratio u+1) := by
  have h1 : u+1 ≠ 0 := by linarith
  have h2 : (1327:ℝ)/200+u ≠ 0 := by linarith
  unfold linearB ratio
  field_simp
  ring

theorem rationalB_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ rationalB u := by
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  have h := splitL_ge_linear hr
  rw [← linearB_ratio hu.1] at h
  have hk : 0 ≤ kept (ratio u) := add_nonneg (gap_nonneg hr) (fresh_nonneg hr)
  unfold rationalB
  linarith only [h,hk]

theorem charged_once (u : ℝ) : remainingA u+remainingB u = cross u+tails u := by
  unfold remainingA remainingB cross crossA crossB tails
  rw [rationalB_exact]
  ring

theorem cross_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ cross u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  exact add_nonneg
    (mul_nonneg (div_nonneg (add_nonneg (gap_nonneg hx) (fresh_nonneg hx)) hu0)
      (rationalB_nonneg hu))
    (mul_nonneg (div_nonneg (factors_nonneg hu).1 hu0)
      (add_nonneg (gap_nonneg hr) (fresh_nonneg hr)))

theorem tails_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ tails u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  exact add_nonneg
    (mul_nonneg (div_nonneg (FreshRemainingFactors.tails_nonneg hx) hu0) (log_nonneg hr))
    (mul_nonneg (div_nonneg (add_nonneg (splitL_nonneg hx)
      (add_nonneg (gap_nonneg hx) (fresh_nonneg hx))) hu0)
      (FreshRemainingFactors.tails_nonneg hr))

end F1FactorCross
