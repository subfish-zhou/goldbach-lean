import E07FifthSourceCover

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

theorem scalar_geometry {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    (1/2-a*s) ∈ Icc (2*a) (2*b) := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hlo := (le_div_iff₀ ha).1 hs.2
  have hhi := (div_le_iff₀ ha).1 hs.1
  constructor <;> linarith only [hlo, hhi]

theorem scalar_reduced_continuous :
    ContinuousOn scalarReduced (Icc s0 FifthClassicalShape.q) := by
  have hp := FifthClassicalShape.parameters
  have hc : ContinuousOn wuLowerCoefficient (Icc s0 FifthClassicalShape.q) := by
    apply truncatedSixthMass_clipped_classical_continuous.continuousOn.congr
    intro s hs
    rw [truncatedSixthMass_clip_eq ⟨by linarith [hp.1, hs.1],
      by linarith [hp.2.2, hs.2]⟩]
  have hz (s : ℝ) (hs : s ∈ Icc s0 FifthClassicalShape.q) :=
    slice_geometry (scalar_geometry hs)
  have hs0 (s : ℝ) (hs : s ∈ Icc s0 FifthClassicalShape.q) : 0 < s := by
    linarith [hp.1, hs.1]
  have hz0 (s : ℝ) (hs : s ∈ Icc s0 FifthClassicalShape.q) : 0 < 1/2-a*s :=
    (hz s hs).2.2.1
  have hl : Continuous (fun s : ℝ => sliceLower (1/2-a*s)) := by
    unfold sliceLower
    fun_prop
  have hr : ContinuousOn
      (fun s : ℝ => ((1/2-a*s)-sliceLower (1/2-a*s))/sliceLower (1/2-a*s))
      (Icc s0 FifthClassicalShape.q) := by
    exact ((by fun_prop : ContinuousOn (fun s : ℝ => 1/2-a*s) _).sub hl.continuousOn).div
      hl.continuousOn (fun s hs => (hz s hs).1.ne')
  unfold scalarReduced
  apply ContinuousOn.mul
  · exact hc.div (by fun_prop) (fun s hs => mul_ne_zero (hs0 s hs).ne' (hz0 s hs).ne')
  · apply hr.log
    intro s hs
    have hh := hz s hs
    exact (div_pos (by linarith [hh.2.1, hh.2.2.1]) hh.1).ne'

theorem scalar_interval_integrable :
    IntervalIntegrable scalarReduced volume s0 FifthClassicalShape.q := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le FifthClassicalShape.parameters.2.1.le]
  exact scalar_reduced_continuous

theorem upper_branch_literal {s : ℝ} (hs : s ∈ Icc geometricSplit FifthClassicalShape.q) :
    scalarReduced s = upperBranch s := by
  have hp := fixed_breakpoints
  have hlo : s0 ≤ s := by linarith [hp.2.2.2.1, hp.2.2.2.2.1, hs.1]
  have hza : 1/2-a*s-b ≤ a := by
    have h := (div_le_iff₀ truncatedSixthLower_parameters.1).1 hs.1
    linarith
  unfold scalarReduced sliceLower upperBranch
  rw [max_eq_left hza, paper_a_eq hlo hs.2]

theorem lower_branch_literal {s : ℝ} (hs : s ∈ Icc s0 geometricSplit) :
    scalarReduced s = lowerBranch s := by
  have hq := fixed_breakpoints.2.2.2.2.2
  rw [scalar_reduced_literal ⟨hs.1, hs.2.trans hq.le⟩, if_pos hs.2]

theorem source_three_integrals :
    Wu08TerminalAlignment.fifthMain =
      4*((∫ s in s0..4, lowerBranch s)+
        (∫ s in (4 : ℝ)..geometricSplit, lowerBranch s)+
        (∫ s in geometricSplit..FifthClassicalShape.q, upperBranch s)) := by
  have hp := fixed_breakpoints
  have hs4 : s0 ≤ 4 := hp.2.2.2.1.le
  have h4g : (4 : ℝ) ≤ geometricSplit := hp.2.2.2.2.1.le
  have hgq : geometricSplit ≤ FifthClassicalShape.q := hp.2.2.2.2.2.le
  have hi1 : IntervalIntegrable scalarReduced volume s0 4 :=
    scalar_interval_integrable.mono_set (by
      rw [uIcc_of_le hs4, uIcc_of_le FifthClassicalShape.parameters.2.1.le]
      exact Icc_subset_Icc le_rfl (h4g.trans hgq))
  have hi2 : IntervalIntegrable scalarReduced volume 4 geometricSplit :=
    scalar_interval_integrable.mono_set (by
      rw [uIcc_of_le h4g, uIcc_of_le FifthClassicalShape.parameters.2.1.le]
      exact Icc_subset_Icc hs4 hgq)
  have hi3 : IntervalIntegrable scalarReduced volume geometricSplit FifthClassicalShape.q :=
    scalar_interval_integrable.mono_set (by
      rw [uIcc_of_le hgq, uIcc_of_le FifthClassicalShape.parameters.2.1.le]
      exact Icc_subset_Icc (hs4.trans h4g) le_rfl)
  have h12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have h123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  have he1 : (∫ s in s0..4, scalarReduced s) = ∫ s in s0..4, lowerBranch s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hs4] at hs
    exact lower_branch_literal ⟨hs.1, hs.2.trans h4g⟩
  have he2 : (∫ s in (4 : ℝ)..geometricSplit, scalarReduced s) =
      ∫ s in (4 : ℝ)..geometricSplit, lowerBranch s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le h4g] at hs
    exact lower_branch_literal ⟨hs4.trans hs.1, hs.2⟩
  have he3 : (∫ s in geometricSplit..FifthClassicalShape.q, scalarReduced s) =
      ∫ s in geometricSplit..FifthClassicalShape.q, upperBranch s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hgq] at hs
    exact upper_branch_literal hs
  rw [scalar_parameter_transport]
  linarith only [h12, h123, he1, he2, he3]

theorem initial_branch_formula {s : ℝ} (hs : s ∈ Icc s0 4) :
    lowerBranch s =
      log (s-1)/(s*(1/2-a*s))*log (b/(1/2-a*s-b)) := by
  simp only [lowerBranch, paperA, if_pos hs.2]

theorem recurrence_lower_formula {s : ℝ} (hs : 4 ≤ s) :
    lowerBranch s =
      (log (s-1)+(∫ t in (3 : ℝ)..(s-1),
        (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t)) /
          (s*(1/2-a*s))*log (b/(1/2-a*s-b)) := by
  rcases eq_or_lt_of_le hs with he | he
  · subst s
    norm_num [lowerBranch, paperA]
  · simp only [lowerBranch, paperA, if_neg (not_le.mpr he)]

theorem recurrence_upper_formula {s : ℝ} (hs : 4 ≤ s) :
    upperBranch s =
      (log (s-1)+(∫ t in (3 : ℝ)..(s-1),
        (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t)) /
          (s*(1/2-a*s))*log ((1/2-a*s-a)/a) := by
  rcases eq_or_lt_of_le hs with he | he
  · subst s
    norm_num [upperBranch, paperA]
  · simp only [upperBranch, paperA, if_neg (not_le.mpr he)]

theorem paper_classical_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (paperClassical-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  rw [paper_classical_eq_fifthMain]
  exact fifthPair_actual_lower hε

end
end WuTarget.Wu08FifthSource
