import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set
open scoped Interval

namespace MathlibNt.SieveTheory.SuzukiMainTermNormalization

/-- Derivative used in Suzuki's change of variables `t = log D / log x`. -/
theorem hasDerivAt_log_div_log {D x : ℝ} (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log D / Real.log y)
      (- Real.log D / (x * (Real.log x) ^ 2)) x := by
  convert ((hasDerivAt_const x (Real.log D)).div
    (Real.hasDerivAt_log hx) hlogx) using 1 <;> try rfl
  ring

/-- Exact change of variables behind the dimension-one main term.  This is the
ordinary-integral form of the Stieltjes term `-∫ H(log D/log x) d(log z/log x)`.
The orientation is important: `x : w → z` corresponds to `t : σ → s`. -/
theorem stieltjesMainTerm_changeOfVariables
    {D w z s σ : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hH : Continuous H) :
    (∫ x in w..z,
      H (Real.log D / Real.log x) *
        (Real.log z / (x * (Real.log x) ^ 2))) =
      (1 / s) * ∫ t in s..σ, H t := by
  have hσ : 0 < σ := hs.trans_le hsσ
  have hD0 : 0 < D := lt_trans (by norm_num) hD
  have hlogD : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
  have hzpos : 0 < z := by rw [hz]; positivity
  have hwpos : 0 < w := by rw [hw]; positivity
  have hlogz : Real.log z = Real.log D / s := by
    rw [hz, Real.log_rpow hD0]
    ring
  have hlogw : Real.log w = Real.log D / σ := by
    rw [hw, Real.log_rpow hD0]
    ring
  have hz1 : 1 < z := by
    rw [hz]
    exact Real.one_lt_rpow hD (by positivity)
  have hw1 : 1 < w := by
    rw [hw]
    exact Real.one_lt_rpow hD (by positivity)
  have hwz : w ≤ z := by
    rw [hw, hz]
    exact Real.rpow_le_rpow_of_exponent_le hD.le
      (one_div_le_one_div_of_le hs hsσ)
  let f : ℝ → ℝ := fun x => Real.log D / Real.log x
  let f' : ℝ → ℝ := fun x => - Real.log D / (x * (Real.log x) ^ 2)
  have hf : ∀ x ∈ [[w, z]], HasDerivAt f (f' x) x := by
    intro x hx
    have hxIcc : x ∈ Icc w z := by simpa [uIcc_of_le hwz] using hx
    have hx1 : 1 < x := hw1.trans_le hxIcc.1
    exact hasDerivAt_log_div_log (ne_of_gt (lt_trans (by norm_num) hx1))
      (ne_of_gt (Real.log_pos hx1))
  have hf' : ContinuousOn f' [[w, z]] := by
    intro x hx
    have hxIcc : x ∈ Icc w z := by simpa [uIcc_of_le hwz] using hx
    have hx1 : 1 < x := hw1.trans_le hxIcc.1
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx1)
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    apply ContinuousAt.continuousWithinAt
    dsimp [f']
    exact continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 2))
      (mul_ne_zero hx0 (pow_ne_zero 2 hlogx))
  have hsubst := intervalIntegral.integral_comp_mul_deriv hf hf' hH
  have hfw : f w = σ := by
    dsimp [f]
    rw [hlogw]
    field_simp
  have hfz : f z = s := by
    dsimp [f]
    rw [hlogz]
    field_simp
  rw [hfw, hfz] at hsubst
  calc
    (∫ x in w..z,
        H (Real.log D / Real.log x) *
          (Real.log z / (x * (Real.log x) ^ 2))) =
        (-1 / s) * ∫ x in w..z, (H ∘ f) x * f' x := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp [f, f']
          rw [hlogz]
          field_simp
    _ = (-1 / s) * ∫ t in σ..s, H t := by rw [hsubst]
    _ = (1 / s) * ∫ t in s..σ, H t := by
      rw [intervalIntegral.integral_symm]
      ring

end MathlibNt.SieveTheory.SuzukiMainTermNormalization
