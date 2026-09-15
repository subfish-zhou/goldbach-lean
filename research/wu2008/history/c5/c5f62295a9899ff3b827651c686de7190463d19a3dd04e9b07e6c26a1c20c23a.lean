import SrcFifthGainAnalyticEnvelope

namespace WuSource.SrcFifthGain.Analytic
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def lowerMass (l r : ℝ) : ℝ :=
  lowerSlope l*((r-s0)^2-(l-s0)^2)/2
def upperMass (l r : ℝ) : ℝ :=
  upperSlope l*((FifthClassicalShape.q-l)^2-(FifthClassicalShape.q-r)^2)/2

theorem linear_left_integral (L l r : ℝ) :
    (∫ s in l..r, s-L) = ((r-L)^2-(l-L)^2)/2 := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => (s-L)^2/2) (s-L) s := by
    convert ((((hasDerivAt_id s).sub_const L).pow 2).div_const 2) using 1 <;> ring
  have hi : IntervalIntegrable (fun s : ℝ => s-L) volume l r := by
    exact (continuous_id.sub continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi]
  ring

theorem linear_right_integral (U l r : ℝ) :
    (∫ s in l..r, U-s) = ((U-l)^2-(U-r)^2)/2 := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => -(U-s)^2/2) (U-s) s := by
    convert (((((hasDerivAt_const s U).sub (hasDerivAt_id s)).pow 2).neg).div_const 2)
      using 1 <;> dsimp only [Pi.sub_apply, id_eq] <;> ring
  have hi : IntervalIntegrable (fun s : ℝ => U-s) volume l r := by
    exact (continuous_const.sub continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi]
  ring

theorem lower_mass_le {l r : ℝ} (hl : s0 ≤ l) (hlr : l ≤ r)
    (hr : r ≤ geometricSplit) :
    lowerMass l r ≤ ∫ s in l..r, weight s := by
  have hi : IntervalIntegrable (fun s => lowerSlope l*(s-s0)) volume l r :=
    ((continuous_id.sub continuous_const).const_mul _).intervalIntegrable _ _
  have h := weight_integral_directed hl hlr
    (hr.trans fixed_breakpoints.2.2.2.2.2.le) hi
    (fun _s hs => lower_envelope hl hs.1 (hs.2.trans hr))
  rw [intervalIntegral.integral_const_mul, linear_left_integral] at h
  simpa only [lowerMass, mul_div_assoc] using h

theorem upper_mass_le {l r : ℝ} (hl : geometricSplit ≤ l) (hlr : l ≤ r)
    (hr : r ≤ FifthClassicalShape.q) :
    upperMass l r ≤ ∫ s in l..r, weight s := by
  have hL : s0 ≤ geometricSplit := by
    linarith [fixed_breakpoints.2.2.2.1, fixed_breakpoints.2.2.2.2.1]
  have hi : IntervalIntegrable (fun s => upperSlope l*(FifthClassicalShape.q-s)) volume l r :=
    ((continuous_const.sub continuous_id).const_mul _).intervalIntegrable _ _
  have h := weight_integral_directed (hL.trans hl) hlr hr hi
    (fun _s hs => upper_envelope hl hs.1 (hs.2.trans hr))
  rw [intervalIntegral.integral_const_mul, linear_right_integral] at h
  simpa only [upperMass, mul_div_assoc] using h

def analyticMass (j : ℕ) : ℝ :=
  if j < 6 then lowerMass (cellLower j) (cellUpper j)
  else if j = 6 then lowerMass (node 20) geometricSplit+upperMass geometricSplit (node 21)
  else upperMass (cellLower j) (cellUpper j)

theorem analytic_mass_le {j : ℕ} (hj : j < 13) : analyticMass j ≤ cellWeight j := by
  have hg := cell_geometry hj
  by_cases hj6 : j < 6
  · rw [analyticMass, if_pos hj6]
    apply lower_mass_le hg.1 hg.2.1
    interval_cases j <;>
      norm_num [cellUpper, node, FifthClassicalShape.q, geometricSplit,
        a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  · by_cases he : j = 6
    · subst j
      rw [analyticMass, if_neg (by omega : ¬6 < 6), if_pos rfl]
      have hc := cross_cell
      have hl : s0 ≤ node 20 := hc.1 ▸ hg.1
      have hr : node 21 ≤ FifthClassicalShape.q := hc.2.1 ▸ hg.2.2.1
      have hi1 := weight_integrable_sub hl hc.2.2.1.le (hc.2.2.2.le.trans hr)
      have hi2 := weight_integrable_sub (hl.trans hc.2.2.1.le) hc.2.2.2.le hr
      have hm1 := lower_mass_le hl hc.2.2.1.le le_rfl
      have hm2 := upper_mass_le le_rfl hc.2.2.2.le hr
      have hadd := add_le_add hm1 hm2
      rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2] at hadd
      simpa only [cellWeight, hc.1, hc.2.1] using hadd
    · rw [analyticMass, if_neg hj6, if_neg he]
      apply upper_mass_le _ hg.2.1 hg.2.2.1
      have hj7 : 7 ≤ j := by omega
      interval_cases j <;>
        norm_num [cellLower, node, s0, geometricSplit,
          a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

end
end WuSource.SrcFifthGain.Analytic
