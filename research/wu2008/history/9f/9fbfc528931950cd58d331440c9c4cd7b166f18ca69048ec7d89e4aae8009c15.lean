import SrcFifthGainTransport

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def lowerWeight (s : ℝ) : ℝ :=
  log (2*b/(1-2*b-2*a*s))/(s*(1-2*a*s))

def upperWeight (s : ℝ) : ℝ :=
  log (1/(2*a)-1-s)/(s*(1-2*a*s))

theorem weight_bounds {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    0 ≤ weight s ∧ weight s ≤ 1 := by
  have h := reduced_weight_bounds hs
  unfold weight
  constructor <;> linarith [h.1, h.2]

theorem weight_continuous :
    ContinuousOn weight (Icc s0 FifthClassicalShape.q) :=
  reduced_weight_continuous.div_const 2

theorem weight_integrable :
    IntervalIntegrable weight volume s0 FifthClassicalShape.q := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le FifthClassicalShape.parameters.2.1.le]
  exact weight_continuous

theorem weight_integrable_sub {l r : ℝ} (hl : s0 ≤ l) (hlr : l ≤ r)
    (hr : r ≤ FifthClassicalShape.q) : IntervalIntegrable weight volume l r := by
  apply weight_integrable.mono_set
  rw [uIcc_of_le hlr, uIcc_of_le FifthClassicalShape.parameters.2.1.le]
  exact Icc_subset_Icc hl hr

theorem weight_lower {s : ℝ} (hs : s ∈ Icc s0 geometricSplit) :
    weight s = lowerWeight s := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hza : a ≤ 1/2-a*s-b := by
    have h := (le_div_iff₀ ha).1 hs.2
    linarith
  unfold weight reducedWeight sliceLower lowerWeight
  rw [max_eq_right hza,
    show (1/2-a*s)-(1/2-a*s-b)=b by ring,
    show (1 : ℝ)-2*b-2*a*s=2*(1/2-a*s-b) by ring,
    show (1 : ℝ)-2*a*s=2*(1/2-a*s) by ring,
    mul_div_mul_left b (1/2-a*s-b) (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem weight_upper {s : ℝ} (hs : s ∈ Icc geometricSplit FifthClassicalShape.q) :
    weight s = upperWeight s := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hza : 1/2-a*s-b ≤ a := by
    have h := (div_le_iff₀ ha).1 hs.1
    linarith
  have he : ((1/2-a*s)-a)/a = 1/(2*a)-1-s := by
    field_simp [ha.ne']
    ring
  unfold weight reducedWeight sliceLower upperWeight
  rw [max_eq_left hza, he,
    show (1 : ℝ)-2*a*s=2*(1/2-a*s) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem lower_integral_literal {l r : ℝ} (hl : s0 ≤ l) (hlr : l ≤ r)
    (hr : r ≤ geometricSplit) :
    (∫ s in l..r, weight s) = ∫ s in l..r, lowerWeight s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hlr] at hs
  exact weight_lower ⟨hl.trans hs.1, hs.2.trans hr⟩

theorem upper_integral_literal {l r : ℝ} (hl : geometricSplit ≤ l) (hlr : l ≤ r)
    (hr : r ≤ FifthClassicalShape.q) :
    (∫ s in l..r, weight s) = ∫ s in l..r, upperWeight s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hlr] at hs
  exact weight_upper ⟨hl.trans hs.1, hs.2.trans hr⟩

theorem weight_integral_nonneg {l r : ℝ} (hl : s0 ≤ l) (hlr : l ≤ r)
    (hr : r ≤ FifthClassicalShape.q) :
    0 ≤ ∫ s in l..r, weight s :=
  intervalIntegral.integral_nonneg hlr (fun _s hs =>
    (weight_bounds ⟨hl.trans hs.1, hs.2.trans hr⟩).1)

theorem weight_integral_directed {l r : ℝ} (hl : s0 ≤ l) (hlr : l ≤ r)
    (hr : r ≤ FifthClassicalShape.q) {w : ℝ → ℝ}
    (hi : IntervalIntegrable w volume l r)
    (hw : ∀ s ∈ Icc l r, w s ≤ weight s) :
    (∫ s in l..r, w s) ≤ ∫ s in l..r, weight s :=
  intervalIntegral.integral_mono_on hlr hi (weight_integrable_sub hl hlr hr) hw

end
end WuSource.SrcFifthGain
