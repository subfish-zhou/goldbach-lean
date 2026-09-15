import MathlibNt.Wu2008DoubleSieve.SecondFunctionalReciprocalGridBoundary

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped BigOperators Classical

/-- A literal signed simple grid function, extended by zero outside the cube. -/
noncomputable def gridStep {n k : ℕ} (c : GridIndex n k → ℝ) (t : Fin n → ℝ) : ℝ :=
  ∑ a, (gridCell a).indicator (fun _ => c a) t

/-- The actual labelled prime sum, not a definition by cell masses. -/
noncomputable def gridPrimeSum {n k : ℕ} (R : ℝ) (c : GridIndex n k → ℝ) : ℝ :=
  ∑ p : Fin n → primeSlabPrimes R, primeSlabWeight R p * gridStep c (gridCoordinates R p)

/-- The actual weighted Lebesgue integral, not a stipulated quadrature formula. -/
noncomputable def gridIntegral {n k : ℕ} (c : GridIndex n k → ℝ) : ℝ :=
  ∫ t in continuousCube n, gridStep c t * continuousDensity t

theorem gridStep_measurable {n k : ℕ} (c : GridIndex n k → ℝ) : Measurable (gridStep c) := by
  apply Finset.measurable_sum
  intro a _
  exact measurable_const.indicator (gridCell_measurable a)

theorem gridStep_on_cell {n k : ℕ} (c : GridIndex n k → ℝ) (a : GridIndex n k)
    {t : Fin n → ℝ} (ht : t ∈ gridCell a) : gridStep c t = c a := by
  unfold gridStep
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem ht _
  · intro b _ hba
    apply Set.indicator_of_notMem
    intro hb
    exact Set.disjoint_left.mp (gridCell_disjoint hba) hb ht
  · simp

theorem gridStep_off_cube {n k : ℕ} (c : GridIndex n k → ℝ) {t : Fin n → ℝ}
    (ht : t ∉ continuousCube n) : gridStep c t = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  apply Set.indicator_of_notMem
  intro ha
  exact ht (gridClosed_subset_cube a (gridCell_subset_closed a ha))

theorem gridStep_bound {n k : ℕ} (c : GridIndex n k → ℝ) {K : ℝ}
    (hc : ∀ a, |c a| ≤ K) {t : Fin n → ℝ} (ht : t ∈ continuousCube n) : |gridStep c t| ≤ K := by
  obtain ⟨a, ha, _⟩ := gridCell_partition.mp ht
  rw [gridStep_on_cell c a ha]
  exact hc a

theorem gridStep_integrable {n k : ℕ} (c : GridIndex n k → ℝ) :
    IntegrableOn (fun t => gridStep c t * continuousDensity t) (continuousCube n) := by
  apply continuousDensity_mul_integrable (gridStep_measurable c)
    (K := ∑ a, |c a|)
  intro t ht
  rw [Real.norm_eq_abs]
  apply gridStep_bound c _ ht
  intro a
  exact Finset.single_le_sum (fun b _ => abs_nonneg (c b)) (Finset.mem_univ a)

theorem gridPrimeSum_disintegration {n k : ℕ} (R : ℝ) (c : GridIndex n k → ℝ) :
    gridPrimeSum R c = ∑ a, c a * gridDiscreteMass R a := by
  unfold gridPrimeSum gridStep gridDiscreteMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  simp only [Set.indicator_apply]
  split_ifs <;> ring

theorem gridStep_density_eq {n k : ℕ} (c : GridIndex n k → ℝ) (t : Fin n → ℝ) :
    gridStep c t * continuousDensity t =
      ∑ a, c a * (gridCell a).indicator continuousDensity t := by
  unfold gridStep
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Set.indicator_apply]
  split_ifs <;> ring

theorem gridIntegral_disintegration {n k : ℕ} (c : GridIndex n k → ℝ) :
    gridIntegral c = ∑ a, c a * gridContinuousMass a := by
  unfold gridIntegral
  simp_rw [gridStep_density_eq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_const_mul, setIntegral_indicator (gridCell_measurable a)]
    have hs : continuousCube n ∩ gridCell a = gridCell a :=
      Set.inter_eq_right.mpr (fun _ ht => gridClosed_subset_cube a (gridCell_subset_closed a ht))
    rw [hs]
    rfl
  · intro a _
    exact ((continuousDensity_integrable n).indicator (gridCell_measurable a)).const_mul (c a)

/-- The cell count is explicit; the estimate accepts arbitrary signed coefficient tables. -/
theorem gridStep_error {n k : ℕ} (R : ℝ) (c : GridIndex n k → ℝ) {K δ : ℝ}
    (hK : 0 ≤ K) (hc : ∀ a, |c a| ≤ K)
    (hd : ∀ a : GridIndex n k, |gridDiscreteMass R a - gridContinuousMass a| ≤ δ) :
    |gridPrimeSum R c - gridIntegral c| ≤ ((k + 1 : ℝ) ^ n) * K * δ := by
  rw [gridPrimeSum_disintegration, gridIntegral_disintegration, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ a, |c a * (gridDiscreteMass R a - gridContinuousMass a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : GridIndex n k, K * δ := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (hc a) (hd a) (abs_nonneg _) hK
    _ = _ := by simp [mul_assoc]

/-- Fixed n,k,K,epsilon precede T; both the scale and all signed coefficients follow it. -/
theorem gridStep_uniform_epsilon (n k : ℕ) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ c : GridIndex n k → ℝ,
      (∀ a, |c a| ≤ K) → |gridPrimeSum R c - gridIntegral c| < ε := by
  let C : ℝ := (k + 1 : ℝ) ^ n
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := ε / (C * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨T, hT, ht⟩ := gridCell_threshold n δ hδ
  refine ⟨T, hT, ?_⟩
  intro R hR c hc
  have hbound := gridStep_error R c hK hc (fun a => (ht R hR k a).le)
  have hstrict : C * K * δ < C * (K + 1) * δ := by
    apply mul_lt_mul_of_pos_right _ hδ
    exact mul_lt_mul_of_pos_left (by linarith) hC
  have heq : C * (K + 1) * δ = ε := by
    dsimp [δ]
    exact mul_div_cancel₀ ε (ne_of_gt (mul_pos hC (by linarith)))
  exact hbound.trans_lt (hstrict.trans_eq heq)

theorem gridStep_fin4 (k : ℕ) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ c : GridIndex 4 k → ℝ,
      (∀ a, |c a| ≤ K) → |gridPrimeSum R c - gridIntegral c| < ε :=
  gridStep_uniform_epsilon 4 k K ε hK hε

theorem gridStep_fin5 (k : ℕ) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ c : GridIndex 5 k → ℝ,
      (∀ a, |c a| ≤ K) → |gridPrimeSum R c - gridIntegral c| < ε :=
  gridStep_uniform_epsilon 5 k K ε hK hε

theorem gridDiscreteMass_zero_dim (R : ℝ) (k : ℕ) (a : GridIndex 0 k) : gridDiscreteMass R a = 1 := by
  simp [gridDiscreteMass, gridCell_zero_dim, primeSlabWeight]

theorem gridContinuousMass_zero_dim (k : ℕ) (a : GridIndex 0 k) : gridContinuousMass a = 1 := by
  rw [gridContinuousMass, gridCell_zero_dim, ← continuousCube_zero]
  exact continuousCube_integral_zero

theorem gridStep_zero_dim (R : ℝ) (k : ℕ) (c : GridIndex 0 k → ℝ) :
    gridPrimeSum R c = gridIntegral c := by
  rw [gridPrimeSum_disintegration, gridIntegral_disintegration]
  simp only [gridDiscreteMass_zero_dim, gridContinuousMass_zero_dim]

end Wu2008DoubleSieve
