import MathlibNt.Wu2008DoubleSieve.SecondFunctionalReciprocalGrid
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeSlabUnit

namespace Wu2008DoubleSieve
open Set MeasureTheory Filter Real
open scoped BigOperators Topology Classical

noncomputable def gridCoordinates {n : ℕ} (R : ℝ) (p : Fin n → primeSlabPrimes R) : Fin n → ℝ :=
  fun i => log (p i).val / log R
noncomputable def gridDiscreteMass {n k : ℕ} (R : ℝ) (a : GridIndex n k) : ℝ :=
  ∑ p : Fin n → primeSlabPrimes R,
    if gridCoordinates R p ∈ gridCell a then primeSlabWeight R p else 0
noncomputable def gridContinuousMass {n k : ℕ} (a : GridIndex n k) : ℝ :=
  ∫ t in gridCell a, continuousDensity t
noncomputable def gridFaceCoeff {n : ℕ} (j : Fin n) (i : Fin n) : ℝ := if i = j then 1 else 0

theorem gridFaceCoeff_sum {n : ℕ} (j : Fin n) (t : Fin n → ℝ) :
    (∑ i, gridFaceCoeff j i * t i) = t j := by
  classical
  simp [gridFaceCoeff]

theorem gridClosed_missing {n k : ℕ} (a : GridIndex n k) {t : Fin n → ℝ}
    (ht : t ∈ continuousRectangle (gridLower a) (gridUpper a)) (hn : t ∉ gridCell a) :
    ∃ j : Fin n, (a j).val ≠ 0 ∧ t j = gridLower a j := by
  classical
  by_contra! h
  apply hn
  intro i hi
  have hh := ht i hi
  refine ⟨hh.1, hh.2, ?_⟩
  by_cases hz : (a i).val = 0
  · exact Or.inl hz
  · exact Or.inr (lt_of_le_of_ne hh.1 (Ne.symm (h i hz)))

theorem gridClosed_missing_subset {n k : ℕ} (a : GridIndex n k) :
    continuousRectangle (gridLower a) (gridUpper a) \ gridCell a ⊆
      ⋃ j : Fin n, continuousCube n ∩ {t | (a j).val ≠ 0 ∧ t j = gridLower a j} := by
  intro t ht
  obtain ⟨j, hj, he⟩ := gridClosed_missing a ht.1 ht.2
  exact mem_iUnion.mpr ⟨j, gridClosed_subset_cube a ht.1, hj, he⟩

theorem gridFace_null {n : ℕ} (j : Fin n) (b : ℝ) :
    volume (continuousCube n ∩ {t | t j = b}) = 0 := by
  simpa only [gridFaceCoeff_sum] using continuousHyperplane_null j (gridFaceCoeff j) b
    (by simp [gridFaceCoeff])

theorem gridCell_ae_closed {n k : ℕ} (a : GridIndex n k) :
    gridCell a =ᵐ[volume] continuousRectangle (gridLower a) (gridUpper a) := by
  apply ae_eq_set.mpr
  constructor
  · simp [Set.sdiff_eq_empty.mpr (gridCell_subset_closed a)]
  · apply measure_mono_null (gridClosed_missing_subset a)
    apply measure_iUnion_null
    intro j
    apply measure_mono_null (t := continuousCube n ∩ {t | t j = gridLower a j})
    · intro t ht; exact ⟨ht.1, ht.2.2⟩
    · exact gridFace_null j (gridLower a j)

theorem gridContinuousMass_closed {n k : ℕ} (a : GridIndex n k) :
    gridContinuousMass a = ∫ t in continuousRectangle (gridLower a) (gridUpper a), continuousDensity t :=
  setIntegral_congr_set (gridCell_ae_closed a)

theorem gridCell_integrable {n k : ℕ} (a : GridIndex n k) :
    IntegrableOn continuousDensity (gridCell a) :=
  (continuousDensity_integrable n).mono_set
    (fun _ ht => gridClosed_subset_cube a (gridCell_subset_closed a ht))

theorem gridCoordinates_mem {n : ℕ} {R : ℝ} (hR : 1 < R) (p : Fin n → primeSlabPrimes R) :
    gridCoordinates R p ∈ continuousCube n := by
  intro i _
  exact primeSlab_coordinate_mem hR (p i).property

theorem gridWeight_nonneg {n : ℕ} (R : ℝ) (p : Fin n → primeSlabPrimes R) :
    0 ≤ primeSlabWeight R p := by
  apply Finset.prod_nonneg
  intro i _
  positivity

theorem gridClosedMass_eq {n k : ℕ} (R : ℝ) (a : GridIndex n k) :
    primeRectangleMass R (gridLower a) (gridUpper a) =
      ∑ p : Fin n → primeSlabPrimes R,
        if gridCoordinates R p ∈ continuousRectangle (gridLower a) (gridUpper a)
        then primeSlabWeight R p else 0 := by
  classical
  simp only [primeRectangleMass, continuousRectangle, gridCoordinates, Set.mem_pi, mem_univ,
    forall_const]

theorem gridDiscrete_le_closed {n k : ℕ} (R : ℝ) (a : GridIndex n k) :
    gridDiscreteMass R a ≤ primeRectangleMass R (gridLower a) (gridUpper a) := by
  classical
  rw [gridClosedMass_eq, gridDiscreteMass]
  apply Finset.sum_le_sum
  intro p _
  by_cases hc : gridCoordinates R p ∈ gridCell a
  · simp [hc, gridCell_subset_closed a hc]
  · simp only [if_neg hc]
    split_ifs <;> first | exact le_refl 0 | exact gridWeight_nonneg R p

/-- Every excluded atom is charged with its original reciprocal weight, never removed by nullness. -/
theorem gridDiscrete_boundary {n k : ℕ} (R : ℝ) (a : GridIndex n k) :
    primeRectangleMass R (gridLower a) (gridUpper a) - gridDiscreteMass R a ≤
      ∑ j : Fin n, primeSlabMass R (gridFaceCoeff j) (gridLower a j) 0 := by
  classical
  rw [gridClosedMass_eq, gridDiscreteMass, ← Finset.sum_sub_distrib]
  unfold primeSlabMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  simp only [gridFaceCoeff_sum, abs_nonpos_iff, sub_eq_zero]
  have hn (j : Fin n) : 0 ≤ (if gridCoordinates R p j = gridLower a j then primeSlabWeight R p else 0) := by
    split_ifs <;> first | exact le_refl 0 | exact gridWeight_nonneg R p
  change (if gridCoordinates R p ∈ continuousRectangle (gridLower a) (gridUpper a) then _ else _) -
    (if gridCoordinates R p ∈ gridCell a then _ else _) ≤
      ∑ j, if gridCoordinates R p j = gridLower a j then primeSlabWeight R p else 0
  by_cases hc : gridCoordinates R p ∈ gridCell a
  · simp only [if_pos hc, if_pos (gridCell_subset_closed a hc), sub_self]
    exact Finset.sum_nonneg (fun j _ => hn j)
  · rw [if_neg hc, sub_zero]
    split_ifs with hb
    · obtain ⟨j, _, hj⟩ := gridClosed_missing a hb hc
      have hs := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ j)
      simpa only [if_pos hj] using hs
    · exact Finset.sum_nonneg (fun j _ => hn j)

/-- Zero-width slab estimates retain the endpoint discrepancy e(R). -/
theorem gridDiscrete_boundary_eventually (n : ℕ) :
    ∀ᶠ R : ℝ in atTop, ∀ (k : ℕ) (a : GridIndex n k),
      primeRectangleMass R (gridLower a) (gridUpper a) - gridDiscreteMass R a ≤
        (n : ℝ) * 5 ^ (n - 1) * primeOrderedDiscrepancy R := by
  filter_upwards [primeSlab_eventually_uniform] with R h
  intro k a
  refine (gridDiscrete_boundary R a).trans ?_
  calc
    _ ≤ ∑ _j : Fin n, 5 ^ (n - 1) * primeOrderedDiscrepancy R := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_zero, zero_add] using h n (gridFaceCoeff j) (gridLower a j) 0
        (le_refl _) j (by simp [gridFaceCoeff])
    _ = _ := by simp [mul_assoc]

/-- Actual cells, not their overlapping closures, approximate their actual weighted integrals. -/
theorem gridCell_threshold (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (k : ℕ) (a : GridIndex n k),
      |gridDiscreteMass R a - gridContinuousMass a| < ε := by
  obtain ⟨T₀, hT₀, hrect⟩ := primeRectangle_integral_threshold n (ε / 2) (by positivity)
  have he : Tendsto (fun R : ℝ => (n : ℝ) * 5 ^ (n - 1) * primeOrderedDiscrepancy R)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul primeOrderedDiscrepancy_tendsto
  have he' := he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp ((gridDiscrete_boundary_eventually n).and he')
  refine ⟨max T₀ T₁, hT₀.trans_le (le_max_left _ _), ?_⟩
  intro R hR k a
  have hr := (hrect R ((le_max_left _ _).trans hR) (gridLower a) (gridUpper a)
    (fun i => (gridLower_bounds a i).1) (fun i => (gridLower_bounds a i).2.1.le)
    (fun i => (gridLower_bounds a i).2.2)).2
  have hb := hT₁ R ((le_max_right _ _).trans hR)
  have hd := gridDiscrete_le_closed R a
  rw [gridContinuousMass_closed]
  have ht := abs_add_le (gridDiscreteMass R a - primeRectangleMass R (gridLower a) (gridUpper a))
    (primeRectangleMass R (gridLower a) (gridUpper a) -
      ∫ t in continuousRectangle (gridLower a) (gridUpper a), continuousDensity t)
  rw [sub_add_sub_cancel, abs_of_nonpos (sub_nonpos.mpr hd)] at ht
  linarith [hb.1 k a, hb.2]

end Wu2008DoubleSieve
