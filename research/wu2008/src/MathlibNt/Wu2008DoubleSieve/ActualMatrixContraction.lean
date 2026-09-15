import MathlibNt.Wu2008DoubleSieve.ActualMatrixContractionIntegral

/-! Pure whole-domain contraction of the original four-row integral matrix. -/
namespace Wu2008DoubleSieve.ActualMatrixContraction
open Set Real MeasureTheory MotherPair SecondFunctionalPositive SecondFunctionalCoupledFeedback
open SecondFunctionalParameters
open scoped Classical Interval BigOperators

/-- These are bounds on the fixed original endpoints, not evaluated integral entries. -/
theorem actual_endpoint_bounds (i : Fin 4) (j : Term) :
    (11/50:ℝ) ≤ 1/(parameters i).S ∧
    upperP (parameters i) j ≤ 7/20 ∧ upperQ (parameters i) j ≤ 5/12 := by
  cases j <;> revert i <;> simp only [Fin.forall_fin_succ] <;>
    dsimp [parameters, upperP, upperQ] <;>
    norm_num [row1, row2, row3, row4]

/-- A single rational lower bound for the denominator on every original pair domain. -/
theorem actual_pair_kernel_bound (i : Fin 4) (j : Term) (t u : ℝ)
    (hr : PairRegion (parameters i) j t u) : 1/(t*u*(1-t-u)) ≤ 100 := by
  have hp := parameters_analytic i
  have he := actual_endpoint_bounds i j
  have h := (pairRegion_iff hp j t u).mp hr
  have ht : (11/50:ℝ) ≤ t := he.1.trans h.1.1
  have hu : (11/50:ℝ) ≤ u := ht.trans ((le_max_right _ _).trans h.2.1)
  have htU : t ≤ 7/20 := h.1.2.trans he.2.1
  have huU : u ≤ 5/12 := h.2.2.trans he.2.2
  have hres : (7/30:ℝ) ≤ 1-t-u := by linarith
  have htu : (11/50:ℝ)*(11/50) ≤ t*u :=
    mul_le_mul ht hu (by norm_num) (by linarith)
  have hd := mul_le_mul htu hres (by norm_num : (0:ℝ) ≤ 7/30) (by nlinarith : 0 ≤ t*u)
  apply (div_le_iff₀ (pair_denominator_bound hp j hr).1).mpr
  nlinarith only [hd]

noncomputable def rectangleArea (p : SecondFunctionalParameters) (j : Term) : ℝ :=
  (upperP p j - 1/p.S) * (upperQ p j - lowerQ p j)

/-- Exact arithmetic on the four original endpoint dictionaries only. -/
theorem actual_rectangle_budget (i : Fin 4) :
    (rectangleArea (parameters i) .gammaFive + rectangleArea (parameters i) .gammaSix +
      rectangleArea (parameters i) .gammaSeven + rectangleArea (parameters i) .gammaEight)*100 ≤ 4 := by
  revert i
  simp only [Fin.forall_fin_succ]
  dsimp [rectangleArea, parameters, upperP, lowerQ, upperQ]
  norm_num [row1, row2, row3, row4]

/-- All four original legal masses are compared on their distinct narrow pair domains. -/
theorem actual_density_mass_bound (i : Fin 4) :
    (∫ v in (1:ℝ)..3, density (parameters i) v) ≤ 4 := by
  have hp := parameters_analytic i
  have h5 := log_mass_rectangle_bound hp .gammaFive (by norm_num : (0:ℝ) ≤ 100)
    (actual_pair_kernel_bound i .gammaFive)
  have h6 := log_mass_rectangle_bound hp .gammaSix (by norm_num : (0:ℝ) ≤ 100)
    (actual_pair_kernel_bound i .gammaSix)
  have h7 := log_mass_rectangle_bound hp .gammaSeven (by norm_num : (0:ℝ) ≤ 100)
    (actual_pair_kernel_bound i .gammaSeven)
  have h8 := log_mass_rectangle_bound hp .gammaEight (by norm_num : (0:ℝ) ≤ 100)
    (actual_pair_kernel_bound i .gammaEight)
  have hi (j : Term) := (feedback_log_integrable hp j).intervalIntegrable (a := 1) (b := 3)
  unfold density
  rw [intervalIntegral.integral_add (((hi .gammaFive).add (hi .gammaSix)).add (hi .gammaSeven))
      (hi .gammaEight),
    intervalIntegral.integral_add ((hi .gammaFive).add (hi .gammaSix)) (hi .gammaSeven),
    intervalIntegral.integral_add (hi .gammaFive) (hi .gammaSix)]
  have hb := actual_rectangle_budget i
  unfold rectangleArea at hb
  linarith only [h5, h6, h7, h8, hb]

/-- The actual matrix is substochastic with a uniform strict margin; no contraction is assumed. -/
theorem actual_matrix_row_sum (i : Fin 4) : (∑ j : Fin 4, matrix i j) ≤ 4/5 := by
  rw [matrix_row_sum_integral]
  have hclip := intervalIntegral.integral_mono_interval (f := density (parameters i))
    (by norm_num : (1:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 25/10)
    (by norm_num : (25/10:ℝ) ≤ 3)
    (Filter.Eventually.of_forall (fun v => density_nonnegative _ (parameters_analytic i) v))
    (density_integrable _ (parameters_analytic i))
  have hmass := actual_density_mass_bound i
  linarith only [hclip, hmass]

theorem actual_matrix_strict_contraction :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ i : Fin 4, (∑ j : Fin 4, matrix i j) ≤ c :=
  ⟨4/5, by norm_num, by norm_num, actual_matrix_row_sum⟩

end Wu2008DoubleSieve.ActualMatrixContraction
