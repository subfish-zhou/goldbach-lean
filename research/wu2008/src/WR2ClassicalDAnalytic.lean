import WR2ClassicalDTable

noncomputable section
namespace WuPaper.ClassicalD
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

def firstValue (s : ℝ) : ℝ := ClassicalQuotient.value C (s-1)
def secondValue (s : ℝ) : ℝ := ClassicalQuotient.first C ClassicalCWeighted.firstValue (s-1)

theorem D_deriv {s : ℝ} (hs : 5 ≤ s) : HasDerivAt D (firstValue s) s := by
  have hc := div_continuous C_continuous
  have h := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (μ := volume) 4 (s-1))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hh := h.comp s ((hasDerivAt_id s).sub_const 1)
  convert hh using 1 <;> first | rfl |
    (simp only [mul_one,max_eq_right (show (1:ℝ) ≤ s-1 by linarith),firstValue,ClassicalQuotient.value])

theorem first_deriv {s : ℝ} (hs : 5 ≤ s) : HasDerivAt firstValue (secondValue s) s := by
  have h := (ClassicalQuotient.value_deriv (by linarith : s-1 ≠ 0)
    (ClassicalCWeighted.C_deriv (by linarith : 4 ≤ s-1))).comp s ((hasDerivAt_id s).sub_const 1)
  convert h using 1 <;> first | rfl | (dsimp [firstValue,secondValue]; ring)

theorem D_bounds {s : ℝ} (hs : 5 ≤ s) (hs6 : s ≤ 6) : 0 ≤ D s ∧ D s ≤ 1 := by
  have hab : (4:ℝ) ≤ s-1 := by linarith
  have hi := (div_continuous C_continuous).intervalIntegrable (μ := volume) 4 (s-1)
  have hk (u : ℝ) (hu : u ∈ Icc (4:ℝ) (s-1)) : 0 ≤ C u/max 1 u ∧ C u/max 1 u ≤ 1 := by
    rw [max_eq_right (show (1:ℝ) ≤ u by linarith [hu.1])]
    have hb := ClassicalCWeighted.C_bounds hu.1 (by linarith [hu.2])
    constructor
    · exact div_nonneg hb.1 (by linarith [hu.1])
    · apply (div_le_iff₀ (by linarith [hu.1])).mpr
      linarith [hu.1]
  have hl := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := (0:ℝ)) (μ := volume)) hi (fun u hu => (hk u hu).1)
  have hh := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (1:ℝ)) (μ := volume)) (fun u hu => (hk u hu).2)
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_zero,mul_one] at hl hh
  change 0 ≤ D s at hl
  change D s ≤ _ at hh
  exact ⟨hl,by linarith only [hh,hs6]⟩

theorem derivative_bounds {s : ℝ} (hs : 5 ≤ s) (hs6 : s ≤ 6) :
    |firstValue s| ≤ 1 ∧ |secondValue s| ≤ (3:ℝ)/4 := by
  have hu : (4:ℝ) ≤ s-1 := by linarith
  have hu0 : 0 < s-1 := by linarith
  have hc := ClassicalCWeighted.C_bounds hu (by linarith)
  have hd := ClassicalCWeighted.derivative_bounds hu (by linarith)
  have hA : |ClassicalCWeighted.firstValue (s-1)/(s-1)| ≤ (1:ℝ)/2 := by
    rw [abs_div,abs_of_pos hu0]
    have h := div_le_div₀ (by norm_num : (0:ℝ) ≤ 2) hd.1 (by norm_num : (0:ℝ) < 4) hu
    norm_num at h
    exact h
  have hB : |C (s-1)/(s-1)^2| ≤ (1:ℝ)/4 := by
    rw [abs_div,abs_of_nonneg hc.1,abs_of_pos (sq_pos_of_pos hu0)]
    apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
    nlinarith only [hc.2,hu]
  constructor
  · unfold firstValue ClassicalQuotient.value
    rw [abs_div,abs_of_nonneg hc.1,abs_of_pos hu0]
    apply (div_le_iff₀ hu0).mpr
    linarith only [hc.2,hu]
  · unfold secondValue ClassicalQuotient.first
    exact (abs_sub _ _).trans (by linarith only [hA,hB])

end WuPaper.ClassicalD
#print axioms WuPaper.ClassicalD.D_deriv
#print axioms WuPaper.ClassicalD.derivative_bounds
