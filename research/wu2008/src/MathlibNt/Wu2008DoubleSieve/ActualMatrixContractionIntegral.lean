import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveMatrix

/-! Exact row concatenation and unweighted transport to the original legal pair domain. -/
namespace Wu2008DoubleSieve.ActualMatrixContraction
open Set Real MeasureTheory MotherPair SecondFunctionalPositive SecondFunctionalCoupledFeedback
open scoped Classical Interval BigOperators

/-- The four entries retain their literal normalization by five. -/
theorem row_sum_integral (p : SecondFunctionalParameters) (hp : AnalyticParameters p) :
    (∑ j : Fin 4, rowEntry p j) = (∫ v in (1:ℝ)..(25/10:ℝ), density p v)/5 := by
  have hi := density_integrable p hp
  have hseg : ∀ k < 4, IntervalIntegrable (density p) volume (grid k) (grid (k+1)) := by
    intro k hk
    exact hi.mono_set (by
      rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
      exact uIcc_subset_Icc (grid_bounds k (by omega)) (grid_bounds (k+1) hk))
  have h := intervalIntegral.sum_integral_adjacent_intervals hseg
  rw [← Fin.sum_univ_eq_sum_range] at h
  simp only [rowEntry, ← Finset.sum_div]
  rw [h]
  norm_num [grid]

theorem matrix_row_sum_integral (i : Fin 4) :
    (∑ j : Fin 4, matrix i j) = (∫ v in (1:ℝ)..(25/10:ℝ), density (parameters i) v)/5 :=
  row_sum_integral (parameters i) (parameters_analytic i)

/-- The unweighted original kernel keeps the original sorted region and both legal gates. -/
noncomputable def pairMask (p : SecondFunctionalParameters) (j : Term) (t u : ℝ) : ℝ :=
  if (t,u) ∈ gainRegion p j then 1/(t*u*(1-t-u)) else 0

theorem pairMask_nonnegative {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (t u : ℝ) : 0 ≤ pairMask p j t u := by
  unfold pairMask
  split_ifs with hr
  · exact one_div_nonneg.mpr (pair_denominator_bound hp j hr.1).1.le
  · exact le_rfl

theorem unweighted_inner_substitution {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (t : ℝ) :
    (∫ u : ℝ, pairMask p j t u) = ∫ v : ℝ, feedbackMasked p j v t := by
  by_cases ht : t ∈ Icc (1/p.S) (upperP p j)
  · have hJ := (feedback_jac_bounds hp j ht).1
    have he (v : ℝ) : feedbackMasked p j v t =
        feedbackJac p j t * pairMask p j t (feedbackU p j v t) := by
      unfold feedbackMasked pairMask feedbackDensity
      split_ifs <;> ring
    simp_rw [he]
    rw [integral_const_mul]
    change _ = feedbackJac p j t * ∫ v : ℝ,
      (fun w => pairMask p j t ((1-t)-w)) (feedbackJac p j t*v)
    rw [Measure.integral_comp_mul_left (fun w => pairMask p j t ((1-t)-w)), smul_eq_mul,
      abs_of_pos (inv_pos.mpr hJ),
      integral_sub_left_eq_self (fun u => pairMask p j t u) volume (1-t)]
    rw [← mul_assoc, mul_inv_cancel₀ hJ.ne', one_mul]
  · have hg (u : ℝ) : pairMask p j t u = 0 := by
      apply if_neg
      exact fun hr => ht ((pairRegion_iff hp j t u).mp hr.1).1
    have hm (v : ℝ) : feedbackMasked p j v t = 0 := by
      apply if_neg
      exact fun hr => ht ((pairRegion_iff hp j t _).mp hr.1).1
    simp only [hg, hm, integral_zero]

/-- Fubini and the actual inverse affine map, not a supplied integral formula. -/
theorem log_mass_original_domain {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) :
    (∫ v in (1:ℝ)..3, feedbackLogKernel p j v) = ∫ t : ℝ, ∫ u : ℝ, pairMask p j t u := by
  simp_rw [← feedback_kernel_log hp j]
  rw [← truncatedSixthMass_integral_eq_interval (by norm_num : (1:ℝ) ≤ 3)
    (feedback_kernel_support hp j)]
  change (∫ v : ℝ, ∫ t : ℝ, feedbackMasked p j v t) = _
  rw [integral_integral_swap (feedback_masked_integrable hp j)]
  simp_rw [← unweighted_inner_substitution hp j]

/-- Bounded nonnegative functions supported on one interval have the elementary width bound. -/
theorem integral_width_bound {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hs : Function.support f ⊆ Icc a b) (h0 : ∀ x, 0 ≤ f x) (hC : ∀ x, f x ≤ C) :
    (∫ x : ℝ, f x) ≤ (b-a)*C := by
  rw [truncatedSixthMass_integral_eq_interval hab hs]
  have h := integral_mono_of_nonneg (μ := volume.restrict (Ioc a b))
    (Filter.Eventually.of_forall h0)
    (intervalIntegrable_const (a := a) (b := b) (c := C)).1
    (Filter.Eventually.of_forall hC)
  simpa only [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const,
    smul_eq_mul] using h

/-- A whole original-domain comparison; no entrywise values or quadrature are used. -/
theorem log_mass_rectangle_bound {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t u, PairRegion p j t u → 1/(t*u*(1-t-u)) ≤ C) :
    (∫ v in (1:ℝ)..3, feedbackLogKernel p j v) ≤
      (upperP p j - 1/p.S) * (upperQ p j - lowerQ p j) * C := by
  rw [log_mass_original_domain hp j]
  have he := gain_endpoint_order hp j
  have hinner (t : ℝ) : (∫ u : ℝ, pairMask p j t u) ≤
      (upperQ p j - lowerQ p j)*C := by
    apply integral_width_bound he.2.2.2.2.1
    · intro u hu
      have hr : (t,u) ∈ gainRegion p j := by
        by_contra hn
        exact hu (if_neg hn)
      have h := ((pairRegion_iff hp j t u).mp hr.1).2
      exact ⟨(le_max_left _ _).trans h.1, h.2⟩
    · exact pairMask_nonnegative hp j t
    · intro u
      unfold pairMask
      split_ifs with hr
      · exact hbound t u hr.1
      · exact hC
  have hs : Function.support (fun t => ∫ u : ℝ, pairMask p j t u) ⊆
      Icc (1/p.S) (upperP p j) := by
    intro t ht
    by_contra hn
    have hz (u : ℝ) : pairMask p j t u = 0 := by
      apply if_neg
      exact fun hr => hn ((pairRegion_iff hp j t u).mp hr.1).1
    exact ht (by simp only [hz, integral_zero])
  exact (integral_width_bound he.2.1 hs
    (fun t => integral_nonneg (pairMask_nonnegative hp j t)) hinner).trans_eq (by ring)

end Wu2008DoubleSieve.ActualMatrixContraction
