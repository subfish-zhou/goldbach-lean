import F1UnpaidJointAssembly

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1RemainingRecovery F1UnpaidRecovery
open scoped Interval
namespace F1FixedSquareRecovery

/-- The right endpoint is forced by the original integration domain. -/
def qEnd : ℝ := momentDenom (927/200)

/-- The exact discarded square, at the original fixed momentA. -/
theorem fixed_square_identity {u : ℝ} (hq : momentDenom u ≠ 0) :
    2*momentWeight u/momentDenom u -
      (4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u)) =
    2*momentWeight u*(1-momentA*momentDenom u)^2/momentDenom u := by
  field_simp
  ring

theorem denominator_bounds {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 < momentDenom u ∧ momentDenom u ≤ qEnd := by
  have hu0 : 0 < u := by linarith [hu.1]
  constructor
  · unfold momentDenom
    positivity
  · unfold momentDenom qEnd
    dsimp only [momentDenom]
    gcongr <;> linarith [hu.1,hu.2]

theorem qEnd_pos : 0 < qEnd := by norm_num [qEnd,momentDenom]

/-- Recover the full forced polynomial lower bound, without selecting a new parameter. -/
def squareLower (u : ℝ) : ℝ := 2*momentWeight u*(1-momentA*momentDenom u)^2/qEnd

theorem fixed_square_lower {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (4*momentA*momentWeight u-2*momentA^2*(momentWeight u*momentDenom u)) +
      squareLower u ≤ 2*momentWeight u/momentDenom u := by
  obtain ⟨hq,hqe⟩ := denominator_bounds hu
  have hw : 0 ≤ momentWeight u := by
    unfold momentWeight
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hu.1) _) (sub_nonneg.mpr hu.2)
  have hn : 0 ≤ 2*momentWeight u*(1-momentA*momentDenom u)^2 := by positivity
  have h := div_le_div_of_nonneg_left hn hq hqe
  rw [← fixed_square_identity hq.ne'] at h
  unfold squareLower
  linarith only [h]

end F1FixedSquareRecovery
