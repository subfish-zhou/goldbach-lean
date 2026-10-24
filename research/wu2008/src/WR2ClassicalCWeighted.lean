import WR2ClassicalCTable

noncomputable section
namespace WuPaper.ClassicalCWeighted
open Real Set MeasureTheory Wu08OriginalFirstSteps
open scoped Interval

def firstValue (s : ℝ) : ℝ := ClassicalQuotient.value B (s-1)
def secondValue (s : ℝ) : ℝ := ClassicalQuotient.first B ClassicalB.firstValue (s-1)

theorem C_deriv {s : ℝ} (hs : 4 ≤ s) : HasDerivAt C (firstValue s) s := by
  have hc := div_continuous B_continuous
  have h := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (μ := volume) 3 (s-1))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hh := h.comp s ((hasDerivAt_id s).sub_const 1)
  convert hh using 1 <;> first | rfl |
    (simp only [mul_one,
      max_eq_right (show (1:ℝ) ≤ s-1 by linarith),firstValue,ClassicalQuotient.value])

theorem first_deriv {s : ℝ} (hs : 4 ≤ s) : HasDerivAt firstValue (secondValue s) s := by
  have h := (ClassicalQuotient.value_deriv (by linarith : s-1 ≠ 0)
    (ClassicalB.B_deriv (by linarith : 3 ≤ s-1))).comp s ((hasDerivAt_id s).sub_const 1)
  convert h using 1 <;> first | rfl | (dsimp [firstValue,secondValue]; ring)

theorem C_bounds {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) : 0 ≤ C s ∧ C s ≤ 4 := by
  have hab : (3:ℝ) ≤ s-1 := by linarith
  have hi := (div_continuous B_continuous).intervalIntegrable (μ := volume) 3 (s-1)
  have hk (u : ℝ) (hu : u ∈ Icc (3:ℝ) (s-1)) : 0 ≤ B u/max 1 u ∧ B u/max 1 u ≤ 2 := by
    rw [max_eq_right (show (1:ℝ) ≤ u by linarith [hu.1])]
    have hb := ClassicalB.B_bounds hu.1 (by linarith [hu.2])
    constructor
    · exact div_nonneg hb.1 (by linarith [hu.1])
    · apply (div_le_iff₀ (by linarith [hu.1])).mpr
      linarith [hu.1]
  have hl := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := (0:ℝ)) (μ := volume)) hi (fun u hu => (hk u hu).1)
  have hh := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := (2:ℝ)) (μ := volume)) (fun u hu => (hk u hu).2)
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_zero] at hl hh
  change 0 ≤ C s at hl
  change C s ≤ _ at hh
  exact ⟨hl,by linarith only [hh,hs6]⟩

theorem derivative_bounds {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    |firstValue s| ≤ 2 ∧ |secondValue s| ≤ 2 := by
  have hu : (3:ℝ) ≤ s-1 := by linarith
  have hu0 : 0 < s-1 := by linarith
  have hb := ClassicalB.B_bounds hu (by linarith)
  have hk := ClassicalC.left_bounds (by linarith : 2 ≤ s-1-1) (by linarith : s-1-1 ≤ 5)
  have hA : |ClassicalB.firstValue (s-1)/(s-1)| ≤ (2:ℝ)/3 := by
    rw [abs_div,abs_of_pos hu0]
    exact div_le_div₀ (by norm_num) hk.2.1 (by norm_num) hu
  have hB : |B (s-1)/(s-1)^2| ≤ (2:ℝ)/3 := by
    rw [abs_div,abs_of_nonneg hb.1,abs_of_pos (sq_pos_of_pos hu0)]
    apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
    nlinarith only [hb.2,hu]
  constructor
  · unfold firstValue ClassicalQuotient.value
    rw [abs_div,abs_of_nonneg hb.1,abs_of_pos hu0]
    apply (div_le_iff₀ hu0).mpr
    linarith only [hb.2,hu]
  · unfold secondValue ClassicalQuotient.first
    have hh := abs_sub (ClassicalB.firstValue (s-1)/(s-1)) (B (s-1)/(s-1)^2)
    linarith only [hh,hA,hB]

theorem weighted_second_bound {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    |ClassicalQuotient.second C firstValue secondValue s| ≤ 1 := by
  have hc := C_bounds hs hs6
  have hd := derivative_bounds hs hs6
  have h := ClassicalQuotient.second_bound (f := C) (f' := firstValue) (f'' := secondValue)
    (F0 := 4) (by norm_num : (0:ℝ) < 4) hs
    (by rw [abs_of_nonneg hc.1]; exact hc.2) hd.1 hd.2
  norm_num at h
  linarith only [h]

end WuPaper.ClassicalCWeighted
#print axioms WuPaper.ClassicalCWeighted.C_deriv
#print axioms WuPaper.ClassicalCWeighted.weighted_second_bound
