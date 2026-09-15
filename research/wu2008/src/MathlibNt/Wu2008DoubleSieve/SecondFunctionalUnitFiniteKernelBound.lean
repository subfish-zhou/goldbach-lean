import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFiniteKernelCore

open scoped BigOperators Classical Topology
namespace SecondFunctionalUnitFiniteKernel
open SecondFunctionalUnitPrimeFibre Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset Filter

/-- Coordinate bounds come from the actual prime carrier. -/
theorem coordinate_bounds {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) :
    1/10 ≤ coordinate f j ∧ coordinate f j ≤ 1/2 := by
  have hm := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) (1/2 : ℝ))).mp (f j).property
  have hp := coordinate_power hR f j
  constructor
  · apply (rpow_le_rpow_left_iff hR).mp
    rw [hp]
    exact hm.2.1
  · apply (rpow_le_rpow_left_iff hR).mp
    rw [hp]
    exact hm.2.2

theorem mass_eventually :
    ∀ᶠ R : ℝ in atTop, ∀ (n : ℕ) (S : Finset (Fin n → primeSlabPrimes R)),
      (∑ f ∈ S, primeSlabWeight R f) ≤ 5^n := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with R hR hs he
  intro n S
  have hm := primeSlab_interval_mass hR hs
    (by norm_num : (1/10 : ℝ) ≤ 1/10) (by norm_num : (1/10 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1/2)
  have hm5 : (∑ p ∈ primeSlabPrimes R, 1/(p : ℝ)) ≤ 5 := by
    unfold primeSlabPrimes
    linarith
  have hsubset : (∑ f ∈ S, primeSlabWeight R f) ≤
      ∑ f : Fin n → primeSlabPrimes R, primeSlabWeight R f :=
    sum_le_sum_of_subset_of_nonneg (subset_univ S) (by
      intro f _ _; unfold primeSlabWeight; positivity)
  have hprod : (∑ f : Fin n → primeSlabPrimes R, primeSlabWeight R f) =
      (∑ p ∈ primeSlabPrimes R, 1/(p : ℝ)) ^ n := by
    simpa only [primeSlabWeight, Fintype.card_fin] using primeSlab_product_mass (α := Fin n) R
  rw [hprod] at hsubset
  exact hsubset.trans (pow_le_pow_left₀ (sum_nonneg (fun p _ => by positivity)) hm5 n)

/-- Same labelled carrier and same reciprocal weights, without quotienting by products. -/
noncomputable def L1 {m : ℕ} (R : ℝ)
    (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ) : ℝ :=
  ∑ f ∈ S, primeSlabWeight R f *
    |weight R (phi - ∑ i, coordinate f i) (coordinate f (Fin.last m)) b -
      F (phi - ∑ i, coordinate f i) (coordinate f (Fin.last m)) b|

/-- Subset comparison for each literal closed finite face, including atoms. -/
theorem faces_subdomain {m : ℕ} (R : ℝ)
    (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b eta : ℝ) :
    (∑ f ∈ S, if |phi - ∑ i, coordinate f i - coordinate f (Fin.last m)| ≤ eta
      then primeSlabWeight R f else 0) ≤ primeSlabUnitLowerMass m R phi eta ∧
    (∑ f ∈ S, if |phi - ∑ i, coordinate f i - b| ≤ eta
      then primeSlabWeight R f else 0) ≤ primeSlabUnitCapMass m R phi b eta := by
  constructor <;> apply sum_le_sum_of_subset_of_nonneg (subset_univ S) <;>
    intro f _ _ <;> split_ifs <;> (try unfold primeSlabWeight) <;> positivity

/-- Both faces are paid by addition; overlap is deliberately harmless. -/
theorem L1_eventually_bound (tau eta : ℝ) (ht : 0 < tau) (ht1 : tau ≤ 1)
    (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop, ∀ (m : ℕ)
      (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ),
      L1 R S phi b ≤ 5^(m+1) * (20*tau + 20*R^(-eta)) +
        60*5^m*(20*eta + primeOrderedDiscrepancy R) := by
  obtain ⟨T,hT,h⟩ := pointwise_threshold tau ht ht1
  filter_upwards [eventually_ge_atTop T, mass_eventually, primeSlab_unit_eventually_uniform]
    with R hRT hmass hfaces
  intro m S phi b
  have hR := hT.trans_le hRT
  have hw (f : Fin (m+1) → primeSlabPrimes R) : 0 ≤ primeSlabWeight R f := by
    unfold primeSlabWeight; positivity
  have hE : 0 ≤ 20*tau + 20*R^(-eta) := by
    have : 0 ≤ R^(-eta) := rpow_nonneg (by linarith) _
    positivity
  have hp := sum_le_sum (s := S) (fun f _ => mul_le_mul_of_nonneg_left
    (h R hRT (phi - ∑ i, coordinate f i) (coordinate f (Fin.last m)) b eta
      (coordinate_bounds hR f (Fin.last m)).1 heta) (hw f))
  have hexpand : (∑ f ∈ S, primeSlabWeight R f *
      ((20*tau + 20*R^(-eta)) +
        (if |phi - ∑ i, coordinate f i - coordinate f (Fin.last m)| ≤ eta then 30 else 0) +
        (if |phi - ∑ i, coordinate f i - b| ≤ eta then 30 else 0))) =
      (20*tau + 20*R^(-eta)) * (∑ f ∈ S, primeSlabWeight R f) +
      30 * (∑ f ∈ S, if |phi - ∑ i, coordinate f i - coordinate f (Fin.last m)| ≤ eta
        then primeSlabWeight R f else 0) +
      30 * (∑ f ∈ S, if |phi - ∑ i, coordinate f i - b| ≤ eta
        then primeSlabWeight R f else 0) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro f hf
    split_ifs <;> ring
  rw [hexpand] at hp
  have hm := mul_le_mul_of_nonneg_left (hmass (m+1) S) hE
  have hf := faces_subdomain R S phi b eta
  have hf' := hfaces m phi b eta heta.le
  have hl := hf.1.trans hf'.1
  have hc := hf.2.trans hf'.2
  unfold L1
  nlinarith
end SecondFunctionalUnitFiniteKernel
