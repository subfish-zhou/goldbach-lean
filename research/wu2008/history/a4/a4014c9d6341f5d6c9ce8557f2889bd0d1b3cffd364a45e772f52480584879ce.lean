import RMapMFifthInputs

namespace WuPaper.RMapMFifth
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open WuTarget.Wu08FifthSource WuSource.SrcFifthGain
open scoped Interval
noncomputable section

theorem source_parameter_branches {t u : ℝ} (ht : t ∈ Icc a b)
    (hu : u ∈ Icc ((1/2-b-t)/a) ((1/2-2*t)/a)) :
    2 < u ∧ u < 6 ∧
      (u ≤ 4 → wuLowerCoefficient u = log (u-1)) ∧
      (4 ≤ u → wuLowerCoefficient u = log (u-1) +
        ∫ v in (3 : ℝ)..(u-1), (∫ w in (2 : ℝ)..(v-1), log (w-1)/w)/v) := by
  have hr := parameter_range ht hu
  have hl : (2 : ℝ) < s0 := by rw [fixed_breakpoints.1]; norm_num
  have hh : FifthClassicalShape.q < (6 : ℝ) := by
    rw [fixed_breakpoints.2.2.1]; norm_num
  refine ⟨hl.trans_le hr.1, hr.2.trans_lt hh, ?_, ?_⟩
  · exact fun h4 => coefficient_initial (hl.le.trans hr.1) h4
  · exact fun h4 => coefficient_recurrence h4 (hr.2.trans hh.le)

theorem interval_error {f g : ℝ → ℝ} {l r e : ℝ} (hlr : l ≤ r)
    (hf : IntervalIntegrable f volume l r) (hg : IntervalIntegrable g volume l r)
    (he : ∀ x ∈ Icc l r, |f x-g x| ≤ e) :
    |(∫ x in l..r, f x)-(∫ x in l..r, g x)| ≤ (r-l)*e := by
  have hlo := intervalIntegral.integral_mono_on hlr
    (intervalIntegrable_const (c := -e)) (hf.sub hg)
    (fun x hx => (abs_le.mp (he x hx)).1)
  have hhi := intervalIntegral.integral_mono_on hlr
    (hf.sub hg) (intervalIntegrable_const (c := e))
    (fun x hx => (abs_le.mp (he x hx)).2)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_sub hf hg] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hlo], hhi⟩

private theorem inner_literal {t : ℝ} (ht : 3 ≤ t) :
    (∫ u in (2 : ℝ)..(t-1), log (u-1)/u) = Wu08OriginalFirstSteps.B t := by
  unfold Wu08OriginalFirstSteps.B
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ t-1)] at hu
  exact (Wu08OriginalFirstSteps.k_literal hu.1).symm

private theorem inner_integrable {t : ℝ} (ht : 3 ≤ t) :
    IntervalIntegrable (fun u : ℝ => log (u-1)/u) volume 2 (t-1) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · apply (continuousOn_id.sub continuousOn_const).log
    intro u hu
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ t-1)] at hu
    change u-1 ≠ 0
    linarith [hu.1]
  · exact continuousOn_id
  · intro u hu
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ t-1)] at hu
    linarith [hu.1]

theorem recurrence_inner_error {t e : ℝ} {p : ℝ → ℝ} (ht : 3 ≤ t) (he : 0 ≤ e)
    (hp : IntervalIntegrable (fun u => p u/u) volume 2 (t-1))
    (herr : ∀ u ∈ Icc 2 (t-1), |log (u-1)-p u| ≤ e) :
    |(∫ u in (2 : ℝ)..(t-1), log (u-1)/u) -
      (∫ u in (2 : ℝ)..(t-1), p u/u)| ≤ (t-3)*(e/2) := by
  have h := interval_error (by linarith : (2 : ℝ) ≤ t-1)
    (inner_integrable ht) hp (e := e/2) ?_
  · convert h using 1; ring
  · intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [← sub_div, abs_div, abs_of_pos hu0]
    exact (div_le_div_of_nonneg_right (herr u hu) hu0.le).trans
      (div_le_div_of_nonneg_left he (by norm_num) hu.1)

private theorem nested_integrable {s : ℝ} (hs : 4 ≤ s) :
    IntervalIntegrable
      (fun t => (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t) volume 3 (s-1) := by
  have hc : Continuous Wu08OriginalFirstSteps.B :=
    continuous_iff_continuousAt.mpr (fun t => (B_derivative t).continuousAt)
  have hi : IntervalIntegrable (fun t => Wu08OriginalFirstSteps.B t/t) volume 3 (s-1) := by
    apply ContinuousOn.intervalIntegrable
    exact hc.continuousOn.div continuousOn_id (by
      intro t ht
      rw [uIcc_of_le (by linarith : (3 : ℝ) ≤ s-1)] at ht
      linarith [ht.1])
  apply hi.congr
  intro t ht
  rw [uIoc_of_le (by linarith : (3 : ℝ) ≤ s-1)] at ht
  dsimp only
  rw [inner_literal ht.1.le]

theorem recurrence_outer_error {s e : ℝ} {p : ℝ → ℝ} (hs : 4 ≤ s) (he : 0 ≤ e)
    (hp : IntervalIntegrable (fun t => p t/t) volume 3 (s-1))
    (herr : ∀ t ∈ Icc 3 (s-1),
      |(∫ u in (2 : ℝ)..(t-1), log (u-1)/u)-p t| ≤ e) :
    |(∫ t in (3 : ℝ)..(s-1), (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t) -
      (∫ t in (3 : ℝ)..(s-1), p t/t)| ≤ (s-4)*(e/3) := by
  have h := interval_error (by linarith : (3 : ℝ) ≤ s-1)
    (nested_integrable hs) hp (e := e/3) ?_
  · convert h using 1; ring
  · intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [← sub_div, abs_div, abs_of_pos ht0]
    exact (div_le_div_of_nonneg_right (herr t ht) ht0.le).trans
      (div_le_div_of_nonneg_left he (by norm_num) ht.1)

theorem coefficient_nested_error {s ell q eLog eInner eOuter : ℝ} {p : ℝ → ℝ}
    (hs : 4 ≤ s) (hs6 : s ≤ 6) (he : 0 ≤ eInner)
    (hp : IntervalIntegrable (fun t => p t/t) volume 3 (s-1))
    (hlog : |log (s-1)-ell| ≤ eLog)
    (hinner : ∀ t ∈ Icc 3 (s-1),
      |(∫ u in (2 : ℝ)..(t-1), log (u-1)/u)-p t| ≤ eInner)
    (houter : |(∫ t in (3 : ℝ)..(s-1), p t/t)-q| ≤ eOuter) :
    |wuLowerCoefficient s-(ell+q)| ≤ eLog+(s-4)*(eInner/3)+eOuter := by
  have hn := recurrence_outer_error hs he hp hinner
  rw [coefficient_recurrence hs hs6]
  apply abs_le.mpr
  rcases abs_le.mp hn with ⟨hnl, hnu⟩
  rcases abs_le.mp hlog with ⟨hll, hlu⟩
  rcases abs_le.mp houter with ⟨hol, hou⟩
  constructor <;> linarith only [hnl, hnu, hll, hlu, hol, hou]

theorem classical_eight_error {p : ℝ → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hp : ContinuousOn p (Icc s0 FifthClassicalShape.q))
    (herr : ∀ s ∈ Icc s0 FifthClassicalShape.q, |wuLowerCoefficient s-p s| ≤ e) :
    |paperClassical-8*(∫ s in s0..FifthClassicalShape.q, p s*weight s)| ≤ 10*e := by
  have h := coefficient_error_transport he hp herr
  have hid : (∫ s in s0..FifthClassicalShape.q, p s*reducedWeight s) =
      2*(∫ s in s0..FifthClassicalShape.q, p s*weight s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    unfold weight
    ring
  rw [hid, ← paper_classical_eq_fifthMain] at h
  convert h using 1; ring

theorem classical_directed_lower {p : ℝ → ℝ} {e q rho : ℝ} (he : 0 ≤ e)
    (hp : ContinuousOn p (Icc s0 FifthClassicalShape.q))
    (herr : ∀ s ∈ Icc s0 FifthClassicalShape.q, |wuLowerCoefficient s-p s| ≤ e)
    (hquad : |8*(∫ s in s0..FifthClassicalShape.q, p s*weight s)-q| ≤ rho) :
    q-rho-10*e ≤ paperClassical := by
  have h := classical_eight_error he hp herr
  linarith [(abs_le.mp h).1, (abs_le.mp hquad).1]

set_option pp.fullNames true
#check @source_parameter_branches
#print axioms source_parameter_branches
#check @interval_error
#print axioms interval_error
#check @recurrence_inner_error
#print axioms recurrence_inner_error
#check @recurrence_outer_error
#print axioms recurrence_outer_error
#check @coefficient_nested_error
#print axioms coefficient_nested_error
#check @classical_eight_error
#print axioms classical_eight_error
#check @classical_directed_lower
#print axioms classical_directed_lower

end
end WuPaper.RMapMFifth
