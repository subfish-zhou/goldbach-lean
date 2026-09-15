import WSrcFifthGainAnalyticMass

namespace WuSource.SrcFifthGain.Analytic
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def weightNumerator : ℕ → ℕ
  | 0 => 135
  | 1 => 520
  | 2 => 940
  | 3 => 1390
  | 4 => 1890
  | 5 => 2430
  | 6 => 2770
  | 7 => 2440
  | 8 => 2040
  | 9 => 1600
  | 10 => 1110
  | 11 => 540
  | 12 => 42
  | _ => 0

def rationalWeight (j : ℕ) : ℚ := (weightNumerator j : ℚ)/100000
def realWeight (j : ℕ) : ℝ := (rationalWeight j : ℝ)

theorem rational_weight_pos {j : ℕ} (hj : j < 13) : 0 < rationalWeight j := by
  interval_cases j <;> norm_num [rationalWeight, weightNumerator]

theorem rational_weight_le_mass {j : ℕ} (hj : j < 13) :
    realWeight j ≤ analyticMass j := by
  interval_cases j <;>
    norm_num [realWeight, rationalWeight, weightNumerator, analyticMass, lowerMass, upperMass,
      lowerSlope, upperSlope, denominator, cellLower, cellUpper, node, geometricSplit,
      s0, FifthClassicalShape.q, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem thirteen_rational_weights {j : ℕ} (hj : j < 13) :
    realWeight j ≤ cellWeight j :=
  (rational_weight_le_mass hj).trans (analytic_mass_le hj)

theorem thirteen_positive_weights {j : ℕ} (hj : j < 13) :
    0 < realWeight j ∧ realWeight j ≤ cellWeight j := by
  refine ⟨?_, thirteen_rational_weights hj⟩
  change (0 : ℝ) < (rationalWeight j : ℝ)
  exact_mod_cast rational_weight_pos hj

theorem thirteen_original_indices {i : ℕ} (hi : i ∈ Finset.Ico 15 28) :
    ((rationalWeight (i-15) : ℚ) : ℝ) ≤ cellWeight (i-15) := by
  have hp := Finset.mem_Ico.mp hi
  exact thirteen_rational_weights (by omega)

theorem first_rational_weight : (135/100000 : ℝ) ≤ cellWeight 0 := by
  simpa [realWeight, rationalWeight, weightNumerator] using
    thirteen_rational_weights (j := 0) (by norm_num)

theorem crossing_rational_weight : (2770/100000 : ℝ) ≤
    (∫ s in node 20..geometricSplit, lowerWeight s)+
      ∫ s in geometricSplit..node 21, upperWeight s := by
  have h := thirteen_rational_weights (j := 6) (by norm_num)
  rw [cell_weight_cross] at h
  simpa [realWeight, rationalWeight, weightNumerator] using h

theorem last_rational_weight : (42/100000 : ℝ) ≤ cellWeight 12 := by
  simpa [realWeight, rationalWeight, weightNumerator] using
    thirteen_rational_weights (j := 12) (by norm_num)

end
end WuSource.SrcFifthGain.Analytic
