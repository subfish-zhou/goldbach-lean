import SecondFunctionalUnitPrimeFibreScalar

open scoped BigOperators Classical
namespace SecondFunctionalUnitPrimeFibre
open Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset

noncomputable def coordinate {m : ℕ} {R : ℝ} (f : Fin m → primeSlabPrimes R) (j : Fin m) : ℝ :=
  log (f j).val / log R
noncomputable def prefixProduct {m : ℕ} {R : ℝ} (f : Fin m → primeSlabPrimes R) : ℝ :=
  ∏ j, ((f j).val : ℝ)

theorem label_prime {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) : (f j).val.Prime := by
  exact ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp (f j).property).1

theorem coordinate_power {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) : R ^ coordinate f j = (f j).val :=
  primeOrdered_coordinate_rpow hR (label_prime hR f j)

theorem prefixProduct_pos {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) : 0 < prefixProduct f := by
  apply prod_pos
  intro j _
  exact_mod_cast (label_prime hR f j).pos

theorem prefixProduct_power {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) : prefixProduct f = R ^ (∑ j, coordinate f j) := by
  rw [rpow_sum_of_pos (by linarith : 0 < R)]
  exact prod_congr rfl (fun j _ => (coordinate_power hR f j).symm)

theorem reciprocal_product {m : ℕ} {R : ℝ} (f : Fin m → primeSlabPrimes R) :
    primeSlabWeight R f = 1 / prefixProduct f := by
  simp only [primeSlabWeight, prefixProduct, prod_div_distrib, prod_const_one]

theorem physical_power_eq {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) (phi b : ℝ) :
    physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b) =
      fibre (R ^ coordinate f j) (R ^ min (phi - ∑ i, coordinate f i) b) := by
  have hR0 : 0 < R := by linarith
  rw [physical_eq (prefixProduct_pos hR f) (rpow_nonneg hR0.le _) (rpow_nonneg hR0.le _),
    prefixProduct_power hR f, ← rpow_sub hR0, rpow_min hR, coordinate_power hR f j]

theorem physical_power_card {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) (phi b : ℝ) :
    ((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) =
      count R (phi - ∑ i, coordinate f i) (coordinate f j) b := by
  rw [physical_power_eq hR f j phi b]; rfl

/-- Per literal labelled prefix; the reciprocal product cancels B exactly. -/
theorem reweight_term {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin m → primeSlabPrimes R) (j : Fin m) (phi b : ℝ) :
    log R / R ^ phi * ((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ) =
      primeSlabWeight R f * weight R (phi - ∑ i, coordinate f i) (coordinate f j) b := by
  have hR0 : 0 < R := by linarith
  rw [physical_power_card hR f j phi b, reciprocal_product, prefixProduct_power hR f, weight]
  rw [neg_sub, rpow_sub hR0]
  field_simp [ne_of_gt (rpow_pos_of_pos hR0 (∑ i, coordinate f i))]

/-- Finite counting-to-reciprocal identity: no label quotient, no extra last-coordinate weight. -/
theorem reweight_sum {m : ℕ} {R : ℝ} (hR : 1 < R)
    (S : Finset (Fin m → primeSlabPrimes R)) (j : Fin m) (phi b : ℝ) :
    log R / R ^ phi *
      (∑ f ∈ S, ((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ)) =
      ∑ f ∈ S, primeSlabWeight R f *
        weight R (phi - ∑ i, coordinate f i) (coordinate f j) b := by
  rw [mul_sum]
  exact sum_congr rfl (fun f _ => reweight_term hR f j phi b)

theorem reweight_fin4 {R : ℝ} (hR : 1 < R)
    (S : Finset (Fin 4 → primeSlabPrimes R)) (phi b : ℝ) :
    log R / R ^ phi *
      (∑ f ∈ S, ((physical (prefixProduct f) (R ^ phi) (f (Fin.last 3)).val (R ^ b)).card : ℝ)) =
      ∑ f ∈ S, primeSlabWeight R f *
        weight R (phi - ∑ i, coordinate f i) (coordinate f (Fin.last 3)) b :=
  reweight_sum hR S (Fin.last 3) phi b

theorem reweight_fin5 {R : ℝ} (hR : 1 < R)
    (S : Finset (Fin 5 → primeSlabPrimes R)) (phi b : ℝ) :
    log R / R ^ phi *
      (∑ f ∈ S, ((physical (prefixProduct f) (R ^ phi) (f (Fin.last 4)).val (R ^ b)).card : ℝ)) =
      ∑ f ∈ S, primeSlabWeight R f *
        weight R (phi - ∑ i, coordinate f i) (coordinate f (Fin.last 4)) b :=
  reweight_sum hR S (Fin.last 4) phi b

/-- The same threshold can be applied after choosing any finite labelled subdomain. -/
theorem reweighted_bound_threshold (a tau : ℝ) (ha : 0 < a) (ht : 0 < tau) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (m : ℕ)
      (S : Finset (Fin m → primeSlabPrimes R)) (j : Fin m) (phi b : ℝ),
      (∀ f ∈ S, a ≤ coordinate f j ∧ coordinate f j ≤ b) →
      log R / R ^ phi *
        (∑ f ∈ S, ((physical (prefixProduct f) (R ^ phi) (f j).val (R ^ b)).card : ℝ)) ≤
          ((1+tau)/a) * (∑ f ∈ S, primeSlabWeight R f) := by
  obtain ⟨T,hT,h⟩ := scalar_threshold a tau ha ht
  refine ⟨T,hT,?_⟩
  intro R hRT m S j phi b hS
  rw [reweight_sum (hT.trans_le hRT) S j phi b, mul_sum]
  apply sum_le_sum
  intro f hf
  have hh := (h R hRT (phi - ∑ i, coordinate f i) (coordinate f j) b (hS f hf).1 (hS f hf).2).1.2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
    (show 0 ≤ primeSlabWeight R f by unfold primeSlabWeight; positivity)
end SecondFunctionalUnitPrimeFibre
