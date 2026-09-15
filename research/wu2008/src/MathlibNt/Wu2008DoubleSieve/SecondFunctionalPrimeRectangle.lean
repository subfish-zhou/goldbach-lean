import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeSlabProduct

namespace Wu2008DoubleSieve
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- Labelled closed rectangle: repeated prime coordinates are retained. -/
noncomputable def primeRectangleMass {n : ℕ} (R : ℝ) (A B : Fin n → ℝ) : ℝ :=
  ∑ p : Fin n → primeSlabPrimes R,
    if ∀ i, log (p i).val / log R ∈ Icc (A i) (B i)
    then primeSlabWeight R p else 0

/-- Exact closed-coordinate filtering, without discarding endpoint atoms. -/
theorem primeRectangle_filter {R A B : ℝ} (hR : 1 < R)
    (hA : 1 / 10 ≤ A) (hB : B ≤ 1 / 2) :
    (primeSlabPrimes R).filter (fun p : ℕ => log p / log R ∈ Icc A B) =
      primesIcc (R ^ A) (R ^ B) := by
  classical
  have hR0 : 0 ≤ R := by linarith
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp, ht⟩
    have hprime := ((mem_primesIcc (rpow_nonneg hR0 _)).mp hp).1
    rw [mem_primesIcc (rpow_nonneg hR0 _)]
    refine ⟨hprime, ?_, ?_⟩
    · simpa only [primeOrdered_coordinate_rpow hR hprime] using
        (rpow_le_rpow_of_exponent_le hR.le ht.1)
    · simpa only [primeOrdered_coordinate_rpow hR hprime] using
        (rpow_le_rpow_of_exponent_le hR.le ht.2)
  · intro hp
    have h := (mem_primesIcc (rpow_nonneg hR0 _)).mp hp
    refine ⟨?_, primeSlab_coordinate_mem hR hp⟩
    apply (mem_primesIcc (rpow_nonneg hR0 _)).mpr
    exact ⟨h.1, (rpow_le_rpow_of_exponent_le hR.le hA).trans h.2.1,
      h.2.2.trans (rpow_le_rpow_of_exponent_le hR.le hB)⟩

/-- The coordinate sum is the actual reciprocal sum on the smaller closed interval. -/
theorem primeRectangle_coordinate_sum {R A B : ℝ} (hR : 1 < R)
    (hA : 1 / 10 ≤ A) (hB : B ≤ 1 / 2) :
    (∑ p : primeSlabPrimes R,
      if log p.val / log R ∈ Icc A B then 1 / (p.val : ℝ) else 0) =
      ∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ) := by
  classical
  rw [Finset.sum_coe_sort (primeSlabPrimes R) (fun p : ℕ =>
    if log p / log R ∈ Icc A B then 1 / (p : ℝ) else 0),
    ← Finset.sum_filter, primeRectangle_filter hR hA hB]

/-- Factorization of the literal simultaneous-condition function sum. -/
theorem primeRectangle_factorization {n : ℕ} {R : ℝ} (hR : 1 < R)
    (A B : Fin n → ℝ) (hA : ∀ i, 1 / 10 ≤ A i) (hB : ∀ i, B i ≤ 1 / 2) :
    primeRectangleMass R A B =
      ∏ i, ∑ p ∈ primesIcc (R ^ A i) (R ^ B i), 1 / (p : ℝ) := by
  classical
  unfold primeRectangleMass primeSlabWeight
  have hi (p : Fin n → primeSlabPrimes R) :
      (if ∀ i, log (p i).val / log R ∈ Icc (A i) (B i)
       then ∏ i, 1 / ((p i).val : ℝ) else 0) =
      ∏ i, if log (p i).val / log R ∈ Icc (A i) (B i)
        then 1 / ((p i).val : ℝ) else 0 := by
    rw [Fintype.prod_ite_zero]
    split_ifs <;> rfl
  simp_rw [hi]
  rw [← Fintype.prod_sum (fun i (p : primeSlabPrimes R) =>
    if log p.val / log R ∈ Icc (A i) (B i) then 1 / (p.val : ℝ) else 0)]
  exact prod_congr rfl (fun i _ => primeRectangle_coordinate_sum hR (hA i) (hB i))

/-- No coordinate of Fin 0 is chosen: the unique empty labelled function has weight one. -/
theorem primeRectangle_zero (R : ℝ) (A B : Fin 0 → ℝ) :
    primeRectangleMass R A B = 1 := by
  classical
  simp [primeRectangleMass, primeSlabWeight]

end Wu2008DoubleSieve
