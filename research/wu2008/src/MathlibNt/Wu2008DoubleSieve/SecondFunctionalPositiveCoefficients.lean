import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveStep

/-! Actual integral coefficients and literal sources for the second functional. -/
namespace Wu2008DoubleSieve.SecondFunctionalPositive
open Set MeasureTheory MotherPair SecondFunctionalParameters FourthRowPhiOmega2
open SecondFunctionalCoupledFeedback
open scoped BigOperators Interval

/-- Only the first five values are used. The four right endpoints are 2.2, 2.3, 2.4, 2.5. -/
noncomputable def grid (k : ℕ) : ℝ := if k = 0 then 1 else (21 + (k:ℝ))/10

 theorem grid_zero : grid 0 = 1 := by simp [grid]

 theorem grid_strict : StrictMonoOn grid (Iic 4) := by
  intro i _ j _ hij
  by_cases hi : i = 0
  · subst i
    have hj : j ≠ 0 := by omega
    simp only [grid, ↓reduceIte, if_neg hj]
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  · have hj : j ≠ 0 := by omega
    simp only [grid, if_neg hi, if_neg hj]
    have hijR : (i:ℝ) < j := by exact_mod_cast hij
    linarith

 theorem grid_bounds (k : ℕ) (hk : k ≤ 4) : grid k ∈ Icc (1:ℝ) 3 := by
  by_cases h : k = 0
  · subst k; norm_num [grid]
  · have h0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have h4 : (k:ℝ) ≤ 4 := by exact_mod_cast hk
    simp only [grid, if_neg h, mem_Icc]
    constructor <;> linarith

noncomputable def sample (j : Fin 4) : ℝ := grid (j.val+1)
noncomputable def actualVector (δ : ℝ) (j : Fin 4) : ℝ :=
  wuImprovementLimit true δ (sample j)

/-- This coefficient is an actual integral, not an external numerical hypothesis. -/
noncomputable def rowEntry (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  (∫ v in grid j.val..grid (j.val+1), density p v)/5

noncomputable def tail (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  ∫ v in grid 4..3, wuImprovementLimit true δ v * density p v

/-- All original point gains, all three J terms, and the full same-phi cost remain literal. -/
noncomputable def source (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S - cost p δ)/5

 theorem density_integrable (p : SecondFunctionalParameters) (hp : AnalyticParameters p) :
    IntervalIntegrable (density p) volume 1 3 := by
  exact (((feedback_log_integrable hp .gammaFive).add
    (feedback_log_integrable hp .gammaSix)).add
    (feedback_log_integrable hp .gammaSeven)).add
    (feedback_log_integrable hp .gammaEight) |>.intervalIntegrable

 theorem actual_density_integrable (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * density p v) volume 1 3 := by
  have h := (((feedback_log_actual_integrable hp .gammaFive hδ hδhi).add
    (feedback_log_actual_integrable hp .gammaSix hδ hδhi)).add
    (feedback_log_actual_integrable hp .gammaSeven hδ hδhi)).add
    (feedback_log_actual_integrable hp .gammaEight hδ hδhi)
  simpa only [density, mul_add] using h

 theorem rowEntry_nonnegative (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Fin 4) : 0 ≤ rowEntry p j := by
  apply div_nonneg _ (by norm_num)
  apply intervalIntegral.integral_nonneg
    (grid_strict (by exact Nat.le_of_lt j.isLt) (by exact j.isLt) (Nat.lt_succ_self _)).le
  exact fun v _ => density_nonnegative p hp v

 theorem actualVector_nonnegative {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (j : Fin 4) : 0 ≤ actualVector δ j := by
  have hs := grid_bounds (j.val+1) j.isLt
  exact (wuImprovementLimit_bounds hδ hδhi hs.1 (by linarith [hs.2])).1

 theorem actual_tail_nonnegative (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) : 0 ≤ tail p δ := by
  apply tail_nonnegative _ _ (grid_bounds 4 le_rfl)
  · intro v hv
    exact (wuImprovementLimit_bounds hδ hδhi hv.1 (by linarith [hv.2])).1
  · exact fun v _ => density_nonnegative p hp v

 theorem step_sum_identity (p : SecondFunctionalParameters) (δ : ℝ) :
    (∑ k ∈ Finset.range 4, (∫ v in grid k..grid (k+1), density p v) *
      wuImprovementLimit true δ (grid (k+1))) =
      5 * ∑ j : Fin 4, rowEntry p j * actualVector δ j := by
  simp only [Fin.sum_univ_four, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    rowEntry, actualVector, sample]
  norm_num
  ring

/-- The complete producer supplies integrability and actual antitonicity internally. -/
theorem row_with_tail (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (∑ j : Fin 4, rowEntry p j * actualVector δ j) + source p δ + tail p δ/5 ≤
      wuImprovementLimit true δ p.s := by
  have hdhi : δ < 1/2 := by linarith
  have hs := step_lower_with_tail 4 grid grid_zero grid_strict grid_bounds
    (wuImprovementLimit true δ) (density p)
    (wuImprovementLimit_upper_antitone_initial hδ hdhi)
    (fun v _ => density_nonnegative p hp v)
    (density_integrable p hp) (actual_density_integrable p hp hδ hdhi)
  rw [step_sum_identity] at hs
  have ha := actual_limit p hp hδ hδhi
  dsimp [source, tail, gain] at *
  linarith only [hs, ha]

/-- The tail-free row is a weaker inequality, never a full integral identity. -/
theorem row (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (∑ j : Fin 4, rowEntry p j * actualVector δ j) + source p δ ≤
      wuImprovementLimit true δ p.s := by
  have ht := actual_tail_nonnegative p hp hδ (show δ < 1/2 by linarith)
  have hr := row_with_tail p hp hδ hδhi
  linarith only [ht, hr]

end Wu2008DoubleSieve.SecondFunctionalPositive
