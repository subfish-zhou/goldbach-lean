import E07FifthSourceReduction

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

def paperA (s : ℝ) : ℝ :=
  if s ≤ 4 then log (s-1) else
    log (s-1)+(∫ t in (3 : ℝ)..(s-1),
      (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t)

def geometricSplit : ℝ := (1/2-a-b)/a
def lowerBranch (s : ℝ) : ℝ :=
  paperA s/(s*(1/2-a*s))*log (b/(1/2-a*s-b))
def upperBranch (s : ℝ) : ℝ :=
  paperA s/(s*(1/2-a*s))*log ((1/2-a*s-a)/a)
def scalarReduced (s : ℝ) : ℝ :=
  wuLowerCoefficient s/(s*(1/2-a*s)) *
    log (((1/2-a*s)-sliceLower (1/2-a*s))/sliceLower (1/2-a*s))

theorem paper_a_eq {s : ℝ} (hs : s0 ≤ s) (hq : s ≤ FifthClassicalShape.q) :
    paperA s = wuLowerCoefficient s := by
  have hp := FifthClassicalShape.parameters
  by_cases h4 : s ≤ 4
  · rw [paperA, if_pos h4]
    exact (coefficient_initial (by linarith [hp.1]) h4).symm
  · rw [paperA, if_neg h4]
    exact (coefficient_recurrence (by linarith) (by linarith [hp.2.2])).symm

theorem paper_kernel_literal {t u : ℝ} (ht : t ∈ Icc a b)
    (hu : u ∈ Icc ((1/2-b-t)/a) ((1/2-2*t)/a)) :
    paperKernel t u = paperA u/(t*u*(1-2*t-2*a*u)) := by
  have hr := parameter_range ht hu
  rw [paper_a_eq hr.1 hr.2]
  rfl

theorem paper_a_original_integral :
    paperClassical = 8*∫ t in a..b,
      ∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a),
        paperA u/(t*u*(1-2*t-2*a*u)) := by
  unfold paperClassical
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at ht
  have hi : (1/2-b-t)/a ≤ (1/2-2*t)/a :=
    div_le_div_of_nonneg_right (by linarith [ht.2]) truncatedSixthLower_parameters.1.le
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hi] at hu
  exact paper_kernel_literal ht hu

theorem fixed_breakpoints :
    s0 = (70331/20600 : ℝ) ∧ geometricSplit = (41453/10300 : ℝ) ∧
      FifthClassicalShape.q = (927/200 : ℝ) ∧
      s0 < 4 ∧ (4 : ℝ) < geometricSplit ∧ geometricSplit < FifthClassicalShape.q := by
  norm_num [s0, geometricSplit, FifthClassicalShape.q, a, b,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem scalar_reduced_literal {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    scalarReduced s = if s ≤ geometricSplit then lowerBranch s else upperBranch s := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have he := paper_a_eq hs.1 hs.2
  by_cases hg : s ≤ geometricSplit
  · have hza : a ≤ 1/2-a*s-b := by
      have h := (le_div_iff₀ ha).1 hg
      linarith
    rw [if_pos hg]
    unfold scalarReduced sliceLower lowerBranch
    rw [max_eq_right hza, he]
    congr 3
    ring
  · have hza : 1/2-a*s-b ≤ a := by
      have h := (div_le_iff₀ ha).1 (le_of_not_ge hg)
      linarith
    rw [if_neg hg]
    unfold scalarReduced sliceLower upperBranch
    rw [max_eq_left hza, he]

theorem scalar_parameter_transport :
    Wu08TerminalAlignment.fifthMain =
      4*∫ s in s0..FifthClassicalShape.q, scalarReduced s := by
  have ha : a ≠ 0 := truncatedSixthLower_parameters.1.ne'
  have h := intervalIntegral.integral_comp_sub_mul reducedKernel ha (1/2)
    (a := s0) (b := FifthClassicalShape.q)
  have hlo : (1/2 : ℝ)-a*FifthClassicalShape.q = 2*a := by
    unfold FifthClassicalShape.q
    field_simp [ha]
    ring
  have hhi : (1/2 : ℝ)-a*s0 = 2*b := by
    unfold s0
    field_simp [ha]
    ring
  rw [hlo, hhi, smul_eq_mul] at h
  have hk : (fun s => reducedKernel (1/2-a*s)) = fun s => (1/a)*scalarReduced s := by
    funext s
    unfold reducedKernel scalarReduced
    rw [show (1/2 : ℝ)-(1/2-a*s)=a*s by ring, mul_div_cancel_left₀ s ha]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hk, intervalIntegral.integral_const_mul] at h
  have hh : (∫ s in s0..FifthClassicalShape.q, scalarReduced s) =
      ∫ z in (2*a)..(2*b), reducedKernel z := by
    apply mul_left_cancel₀ (inv_ne_zero ha)
    simpa only [one_div] using h
  rw [fifth_main_one_dimensional, hh]

theorem source_finite_cover :
    Icc s0 FifthClassicalShape.q =
      Icc s0 4 ∪ Icc 4 geometricSplit ∪ Icc geometricSplit FifthClassicalShape.q := by
  have hp := fixed_breakpoints
  ext s
  simp only [mem_Icc, mem_union]
  constructor
  · intro hs
    by_cases h4 : s ≤ 4
    · exact Or.inl (Or.inl ⟨hs.1, h4⟩)
    · by_cases hg : s ≤ geometricSplit
      · exact Or.inl (Or.inr ⟨(lt_of_not_ge h4).le, hg⟩)
      · exact Or.inr ⟨(lt_of_not_ge hg).le, hs.2⟩
  · rintro ((hs | hs) | hs) <;> constructor <;>
      linarith [hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2, hs.1, hs.2]

end
end WuTarget.Wu08FifthSource
