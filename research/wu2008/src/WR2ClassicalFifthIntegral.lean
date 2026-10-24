import WR2ClassicalFifthSource

noncomputable section
namespace WuPaper.ClassicalFifthIntegral
open Real Set MeasureTheory Wu2008DoubleSieve
open WuTarget.Wu08FifthSource ClassicalFifthSource ClassicalFifthKernel

private theorem kernel_continuous {A L L1 : ℝ → ℝ} {a b : ℝ}
    (ha : lo ≤ a) (hb : b ≤ hi) (hA : ContinuousOn A (Icc a b))
    (hL : ∀ s ∈ Icc a b, HasDerivAt L (L1 s) s) : ContinuousOn (kernel A L) (Icc a b) := by
  have hl : ContinuousOn L (Icc a b) := fun s hs => (hL s hs).continuousAt.continuousWithinAt
  have hw : ContinuousOn ClassicalFourth.weight (Icc a b) := by
    intro s hs
    have hslo := ha.trans hs.1
    have hshi := hs.2.trans hb
    exact (ClassicalFourth.weight_deriv (by linarith [geometry.1] : s ≠ 0)
      (by linarith [hshi.trans geometry.2.2.2.2.2] : ClassicalFourth.R-s ≠ 0)).continuousAt.continuousWithinAt
  exact hA.mul (hl.mul hw)

private theorem source_continuous_lower : ContinuousOn scalarReduced (Icc lo cut) := by
  have ha : ContinuousOn wuLowerCoefficient (Icc lo cut) :=
    continuousOn_wuLowerCoefficient.mono (fun s hs => by change 0 < s; linarith [hs.1,geometry.1])
  exact (kernel_continuous le_rfl geometry.2.2.2.1 ha
    (fun _s hs => ClassicalFifthBranch.lower_deriv hs.2)).congr
    (fun _s hs => source_lower_literal hs.1 hs.2)

private theorem source_continuous_upper : ContinuousOn scalarReduced (Icc cut hi) := by
  have ha : ContinuousOn wuLowerCoefficient (Icc cut hi) :=
    continuousOn_wuLowerCoefficient.mono (fun s hs => by
      change 0 < s; linarith [hs.1,geometry.1,geometry.2.1,geometry.2.2.1])
  exact (kernel_continuous (geometry.2.1.trans geometry.2.2.1) le_rfl ha
    (fun _s hs => ClassicalFifthBranch.upper_deriv hs.2)).congr
    (fun _s hs => source_upper_literal hs.1 hs.2)

private theorem kernel_integrable {A A1 L L1 : ℝ → ℝ} {a b : ℝ}
    (ha : lo ≤ a) (hb : b ≤ hi) (hab : a ≤ b)
    (hA : ∀ s ∈ Icc a b, HasDerivAt A (A1 s) s)
    (hL : ∀ s ∈ Icc a b, HasDerivAt L (L1 s) s) :
    IntervalIntegrable (kernel A L) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact kernel_continuous ha hb (fun s hs => (hA s hs).continuousAt.continuousWithinAt) hL

/-- The original fifth slot dominates three smooth polynomial-corrected integrals. -/
theorem fifth_lower :
    4*((∫ s in lo..4, kernel ClassicalFifthProfile.initial ClassicalFifthBranch.lower s)+
      (∫ s in (4:ℝ)..cut, kernel ClassicalFifthProfile.terminal ClassicalFifthBranch.lower s)+
      (∫ s in cut..hi, kernel ClassicalFifthProfile.terminal ClassicalFifthBranch.upper s)) ≤
      Wu08TerminalAlignment.fifthMain := by
  have hi1 : IntervalIntegrable scalarReduced volume lo 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le geometry.2.1]
    exact source_continuous_lower.mono (fun _ hs => ⟨hs.1,hs.2.trans geometry.2.2.1⟩)
  have hi2 : IntervalIntegrable scalarReduced volume 4 cut := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le geometry.2.2.1]
    exact source_continuous_lower.mono (fun _ hs => ⟨geometry.2.1.trans hs.1,hs.2⟩)
  have hi3 : IntervalIntegrable scalarReduced volume cut hi := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le geometry.2.2.2.1]
    exact source_continuous_upper
  have hp1 := kernel_integrable le_rfl (geometry.2.2.1.trans geometry.2.2.2.1) geometry.2.1
    (fun s hs => ClassicalFifthProfile.initial_deriv (by linarith [hs.1,geometry.1]))
    (fun _s hs => ClassicalFifthBranch.lower_deriv (hs.2.trans geometry.2.2.1))
  have hp2 := kernel_integrable geometry.2.1 geometry.2.2.2.1 geometry.2.2.1
    (fun _s hs => ClassicalFifthProfile.terminal_deriv hs.1)
    (fun _s hs => ClassicalFifthBranch.lower_deriv hs.2)
  have hp3 := kernel_integrable (geometry.2.1.trans geometry.2.2.1) le_rfl geometry.2.2.2.1
    (fun _s hs => ClassicalFifthProfile.terminal_deriv (geometry.2.2.1.trans hs.1))
    (fun _s hs => ClassicalFifthBranch.upper_deriv hs.2)
  have h1 := intervalIntegral.integral_mono_on geometry.2.1 hp1 hi1 (fun _s hs => initial_le_source hs.1 hs.2)
  have h2 := intervalIntegral.integral_mono_on geometry.2.2.1 hp2 hi2 (fun _s hs => middle_le_source hs.1 hs.2)
  have h3 := intervalIntegral.integral_mono_on geometry.2.2.2.1 hp3 hi3 (fun _s hs => terminal_le_source hs.1 hs.2)
  rw [scalar_parameter_transport,source_constants.1,source_constants.2.2,
    ← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  linarith only [h1,h2,h3]

end WuPaper.ClassicalFifthIntegral
#print axioms WuPaper.ClassicalFifthIntegral.fifth_lower
