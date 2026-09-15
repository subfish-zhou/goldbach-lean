import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeSlab

namespace Wu2008DoubleSieve
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- The actual finite set of primes in the closed exponent cube. -/
noncomputable def primeSlabPrimes (R : ℝ) :=
  primesIcc (R ^ (1 / 10 : ℝ)) (R ^ (1 / 2 : ℝ))

/-- Reciprocal weight on actual labelled prime functions. -/
noncomputable def primeSlabWeight {n : ℕ} (R : ℝ)
    (p : Fin n → primeSlabPrimes R) : ℝ := ∏ i, 1 / ((p i).val : ℝ)

/-- The original closed affine slab, without ordering or factorial quotients. -/
noncomputable def primeSlabMass {n : ℕ} (R : ℝ) (c : Fin n → ℝ) (γ η : ℝ) : ℝ :=
  ∑ p : Fin n → primeSlabPrimes R,
    if |(∑ i, c i * (log (p i).val / log R)) - γ| ≤ η
    then primeSlabWeight R p else 0

/-- Exact finite product mass, valid even if the prime carrier is empty. -/
theorem primeSlab_product_mass {α : Type*} [Fintype α] [DecidableEq α] (R : ℝ) :
    (∑ p : α → primeSlabPrimes R, ∏ i, 1 / ((p i).val : ℝ)) =
      (∑ p ∈ primeSlabPrimes R, 1 / (p : ℝ)) ^ Fintype.card α := by
  classical
  rw [← Fintype.prod_sum (fun (_ : α) (p : primeSlabPrimes R) => 1 / (p.val : ℝ))]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [Finset.sum_coe_sort (primeSlabPrimes R) (fun p : ℕ => 1 / (p : ℝ))]

/-- Exact disintegration of the labelled finite product at any coordinate. -/
theorem primeSlab_slice {n : ℕ} (R : ℝ) (c : Fin n → ℝ) (γ η : ℝ) (j : Fin n) :
    primeSlabMass R c γ η =
      ∑ q : {i : Fin n // i ≠ j} → primeSlabPrimes R,
        (∏ i, 1 / ((q i).val : ℝ)) *
          ∑ p ∈ (primeSlabPrimes R).filter (fun p : ℕ =>
            |c j * (log p / log R) -
              (γ - ∑ i, c i.val * (log (q i).val / log R))| ≤ η),
            1 / (p : ℝ) := by
  classical
  let F := fun p : Fin n → primeSlabPrimes R =>
    if |(∑ i, c i * (log (p i).val / log R)) - γ| ≤ η
    then ∏ i, 1 / ((p i).val : ℝ) else 0
  let G := fun x : primeSlabPrimes R × ({i : Fin n // i ≠ j} → primeSlabPrimes R) =>
    if |c j * (log x.1.val / log R) +
      (∑ i, c i.val * (log (x.2 i).val / log R)) - γ| ≤ η
    then (1 / (x.1.val : ℝ)) * ∏ i, 1 / ((x.2 i).val : ℝ) else 0
  have he : ∑ p, F p = ∑ x, G x :=
    Fintype.sum_equiv (Equiv.piSplitAt j (fun _ => primeSlabPrimes R)) F G (by
      intro p
      dsimp [F, G, Equiv.piSplitAt_apply]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j,
        Fintype.prod_eq_mul_prod_subtype_ne _ j]
      rfl)
  change (∑ p, F p) = _
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  apply sum_congr rfl
  intro q _
  rw [Finset.mul_sum, Finset.sum_filter]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply sum_congr rfl
  intro p _
  dsimp [G]
  have hr : c j * (log p.val / log R) +
      (∑ i, c i.val * (log (q i).val / log R)) - γ =
      c j * (log p.val / log R) -
      (γ - ∑ i, c i.val * (log (q i).val / log R)) := by ring
  rw [hr]
  split_ifs <;> ring

/-- Uniform finite affine-slab producer. Only the genuine frozen Mertens
start is assumed; neither mass nor discrepancy is supplied by the caller. -/
theorem primeSlab_uniform_bound {n : ℕ} {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (c : Fin n → ℝ) (γ η : ℝ) (hη : 0 ≤ η)
    (j : Fin n) (hc : 1 ≤ |c j|) :
    primeSlabMass R c γ η ≤
      (4 + primeOrderedDiscrepancy R) ^ (n - 1) *
        (20 * η + primeOrderedDiscrepancy R) := by
  classical
  rw [primeSlab_slice R c γ η j]
  have hm := primeSlab_interval_mass hR hs
    (by norm_num : (1 / 10 : ℝ) ≤ 1 / 10)
    (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  have he : 0 ≤ 20 * η + primeOrderedDiscrepancy R :=
    add_nonneg (mul_nonneg (by norm_num) hη) (primeOrderedDiscrepancy_nonneg hR)
  calc
    _ ≤ ∑ q : {i : Fin n // i ≠ j} → primeSlabPrimes R,
        (∏ i, 1 / ((q i).val : ℝ)) * (20 * η + primeOrderedDiscrepancy R) := by
      apply sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (primeSlab_one_coordinate hR hs hc hη)
        (Finset.prod_nonneg (fun i _ => by positivity))
    _ = (∑ p ∈ primeSlabPrimes R, 1 / (p : ℝ)) ^ (n - 1) *
        (20 * η + primeOrderedDiscrepancy R) := by
      rw [← Finset.sum_mul]
      have hcard : Fintype.card {i : Fin n // i ≠ j} = n - 1 := by
        rw [Fintype.card_subtype_compl (fun i : Fin n => i = j)]
        simp only [Fintype.card_fin, Fintype.card_subtype_eq]
      have hmass := primeSlab_product_mass (α := {i : Fin n // i ≠ j}) R
      rw [hcard] at hmass
      exact congrArg (fun x => x * (20 * η + primeOrderedDiscrepancy R)) hmass
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (sum_nonneg (fun p _ => by positivity)) hm _) he

end Wu2008DoubleSieve
