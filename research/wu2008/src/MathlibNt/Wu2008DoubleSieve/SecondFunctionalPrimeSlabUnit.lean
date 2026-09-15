import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeSlabProduct

namespace Wu2008DoubleSieve
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- A single threshold precedes dimension, coefficients, intercept and width. -/
theorem primeSlab_eventually_uniform :
    ∀ᶠ R : ℝ in atTop, ∀ (n : ℕ) (c : Fin n → ℝ) (γ η : ℝ),
      0 ≤ η → ∀ j : Fin n, 1 ≤ |c j| →
      primeSlabMass R c γ η ≤ 5 ^ (n - 1) *
        (20 * η + primeOrderedDiscrepancy R) := by
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with R hR hs he
  intro n c γ η hη j hc
  refine (primeSlab_uniform_bound hR hs c γ η hη j hc).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by linarith [primeOrderedDiscrepancy_nonneg hR]) (by linarith) _)
    (add_nonneg (mul_nonneg (by norm_num) hη) (primeOrderedDiscrepancy_nonneg hR))

/-- Ordered or windowed subsets retain the very same reciprocal weights. -/
theorem primeSlab_subdomain_le {n : ℕ} (R : ℝ) (c : Fin n → ℝ) (γ η : ℝ)
    (S : Finset (Fin n → primeSlabPrimes R))
    (hS : ∀ p ∈ S, |(∑ i, c i * (log (p i).val / log R)) - γ| ≤ η) :
    (∑ p ∈ S, primeSlabWeight R p) ≤ primeSlabMass R c γ η := by
  classical
  have hpos (p : Fin n → primeSlabPrimes R) : 0 ≤ primeSlabWeight R p :=
    prod_nonneg (fun i _ => by positivity)
  calc
    _ = ∑ p ∈ S, if |(∑ i, c i * (log (p i).val / log R)) - γ| ≤ η
        then primeSlabWeight R p else 0 := by
      apply sum_congr rfl
      intro p hp
      rw [if_pos (hS p hp)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ S) (by
      intro p _ _
      split_ifs
      · exact hpos p
      · exact le_rfl)

/-- Unit lower plane has last coefficient two, not an extra reciprocal weight. -/
noncomputable def primeSlabUnitLowerCoeff (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  if i = Fin.last m then 2 else 1

/-- Literal lower-plane closed gate in logarithmic prime coordinates. -/
noncomputable def primeSlabUnitLowerMass (m : ℕ) (R φ η : ℝ) : ℝ :=
  ∑ p : Fin (m + 1) → primeSlabPrimes R,
    if |φ - (∑ i, log (p i).val / log R) - log (p (Fin.last m)).val / log R| ≤ η
    then primeSlabWeight R p else 0

/-- Literal cap-switch closed gate; the cap may move without changing the threshold. -/
noncomputable def primeSlabUnitCapMass (m : ℕ) (R φ b η : ℝ) : ℝ :=
  ∑ p : Fin (m + 1) → primeSlabPrimes R,
    if |φ - (∑ i, log (p i).val / log R) - b| ≤ η
    then primeSlabWeight R p else 0

theorem primeSlabUnitLowerCoeff_sum (m : ℕ) (t : Fin (m + 1) → ℝ) :
    (∑ i, primeSlabUnitLowerCoeff m i * t i) =
      (∑ i, t i) + t (Fin.last m) := by
  classical
  have h (i : Fin (m + 1)) : primeSlabUnitLowerCoeff m i * t i =
      t i + if i = Fin.last m then t i else 0 := by
    unfold primeSlabUnitLowerCoeff
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem primeSlabUnitLowerMass_eq (m : ℕ) (R φ η : ℝ) :
    primeSlabUnitLowerMass m R φ η =
      primeSlabMass R (primeSlabUnitLowerCoeff m) φ η := by
  unfold primeSlabUnitLowerMass primeSlabMass
  apply sum_congr rfl
  intro p _
  rw [primeSlabUnitLowerCoeff_sum]
  have h : φ - (∑ i, log (p i).val / log R) - log (p (Fin.last m)).val / log R =
      -((∑ i, log (p i).val / log R) + log (p (Fin.last m)).val / log R - φ) := by ring
  rw [h, abs_neg]

theorem primeSlabUnitCapMass_eq (m : ℕ) (R φ b η : ℝ) :
    primeSlabUnitCapMass m R φ b η = primeSlabMass R (fun _ : Fin (m + 1) => 1) (φ - b) η := by
  unfold primeSlabUnitCapMass primeSlabMass
  apply sum_congr rfl
  intro p _
  simp only [one_mul]
  have h : φ - (∑ i, log (p i).val / log R) - b =
      -((∑ i, log (p i).val / log R) - (φ - b)) := by ring
  rw [h, abs_neg]

/-- Both moving faces on the actual finite unit prefix cube. -/
theorem primeSlab_unit_faces {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (m : ℕ) (φ b η : ℝ) (hη : 0 ≤ η) :
    primeSlabUnitLowerMass m R φ η ≤
      (4 + primeOrderedDiscrepancy R) ^ m * (20 * η + primeOrderedDiscrepancy R) ∧
    primeSlabUnitCapMass m R φ b η ≤
      (4 + primeOrderedDiscrepancy R) ^ m * (20 * η + primeOrderedDiscrepancy R) := by
  rw [primeSlabUnitLowerMass_eq, primeSlabUnitCapMass_eq]
  constructor
  · simpa only [Nat.add_sub_cancel] using primeSlab_uniform_bound hR hs
      (primeSlabUnitLowerCoeff m) φ η hη (Fin.last m)
      (by norm_num [primeSlabUnitLowerCoeff])
  · simpa only [Nat.add_sub_cancel] using primeSlab_uniform_bound hR hs
      (fun _ : Fin (m + 1) => 1) (φ - b) η hη (Fin.last m) (by norm_num)

/-- Four-dimensional unit prefix: both actual gates, arbitrary moving intercept. -/
theorem primeSlab_unit_four {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (φ b η : ℝ) (hη : 0 ≤ η) :
    primeSlabUnitLowerMass 3 R φ η ≤
      (4 + primeOrderedDiscrepancy R) ^ 3 * (20 * η + primeOrderedDiscrepancy R) ∧
    primeSlabUnitCapMass 3 R φ b η ≤
      (4 + primeOrderedDiscrepancy R) ^ 3 * (20 * η + primeOrderedDiscrepancy R) :=
  primeSlab_unit_faces hR hs 3 φ b η hη

/-- Five-dimensional unit prefix: both actual gates, arbitrary moving intercept. -/
theorem primeSlab_unit_five {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (φ b η : ℝ) (hη : 0 ≤ η) :
    primeSlabUnitLowerMass 4 R φ η ≤
      (4 + primeOrderedDiscrepancy R) ^ 4 * (20 * η + primeOrderedDiscrepancy R) ∧
    primeSlabUnitCapMass 4 R φ b η ≤
      (4 + primeOrderedDiscrepancy R) ^ 4 * (20 * η + primeOrderedDiscrepancy R) :=
  primeSlab_unit_faces hR hs 4 φ b η hη

/-- Joint eventual uniformity for both faces and every positive dimension. -/
theorem primeSlab_unit_eventually_uniform :
    ∀ᶠ R : ℝ in atTop, ∀ (m : ℕ) (φ b η : ℝ), 0 ≤ η →
      primeSlabUnitLowerMass m R φ η ≤ 5 ^ m * (20 * η + primeOrderedDiscrepancy R) ∧
      primeSlabUnitCapMass m R φ b η ≤ 5 ^ m * (20 * η + primeOrderedDiscrepancy R) := by
  filter_upwards [primeSlab_eventually_uniform] with R h
  intro m φ b η hη
  rw [primeSlabUnitLowerMass_eq, primeSlabUnitCapMass_eq]
  constructor
  · simpa only [Nat.add_sub_cancel] using h (m + 1) (primeSlabUnitLowerCoeff m)
      φ η hη (Fin.last m) (by norm_num [primeSlabUnitLowerCoeff])
  · simpa only [Nat.add_sub_cancel] using h (m + 1) (fun _ => 1)
      (φ - b) η hη (Fin.last m) (by norm_num)

end Wu2008DoubleSieve
