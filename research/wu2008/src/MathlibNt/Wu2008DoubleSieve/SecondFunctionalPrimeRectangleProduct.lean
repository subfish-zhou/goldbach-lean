import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeRectangle

namespace Wu2008DoubleSieve
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- Structural product perturbation with exactly n-1 remaining factors. -/
theorem primeRectangle_product_difference (n : ℕ) (a b : Fin n → ℝ)
    (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (ha : ∀ i, |a i| ≤ M) (hb : ∀ i, |b i| ≤ M)
    (hd : ∀ i, |a i - b i| ≤ e) :
    |(∏ i, a i) - ∏ i, b i| ≤ (n : ℝ) * e * M ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hp : |∏ i : Fin k, a i.succ| ≤ M ^ k := by
      rw [Finset.abs_prod]
      simpa using (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin k)))
        (fun i _ => abs_nonneg (a i.succ)) (fun i _ => ha i.succ))
    have ht := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ) (fun i => hd i.succ)
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have hid : a 0 * (∏ i : Fin k, a i.succ) - b 0 * (∏ i : Fin k, b i.succ) =
        (a 0 - b 0) * (∏ i : Fin k, a i.succ) +
        b 0 * ((∏ i : Fin k, a i.succ) - ∏ i : Fin k, b i.succ) := by ring
    rw [hid]
    calc
      _ ≤ |a 0 - b 0| * |∏ i : Fin k, a i.succ| +
          |b 0| * |(∏ i : Fin k, a i.succ) - ∏ i : Fin k, b i.succ| := by
        simpa only [abs_mul] using abs_add_le
          ((a 0 - b 0) * (∏ i : Fin k, a i.succ))
          (b 0 * ((∏ i : Fin k, a i.succ) - ∏ i : Fin k, b i.succ))
      _ ≤ e * M ^ k + M * ((k : ℝ) * e * M ^ (k - 1)) :=
        add_le_add (mul_le_mul (hd 0) hp (abs_nonneg _) he)
          (mul_le_mul (hb 0) ht (abs_nonneg _) hM)
      _ = _ := by
        cases k with
        | zero => simp
        | succ k => simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]; ring

/-- Uniform discrepancy for the actual prime-function rectangle, with closed atoms. -/
theorem primeRectangle_discrepancy {n : ℕ} {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (A B : Fin n → ℝ) (hA : ∀ i, 1 / 10 ≤ A i)
    (hAB : ∀ i, A i ≤ B i) (hB : ∀ i, B i ≤ 1 / 2) :
    |primeRectangleMass R A B - ∏ i, ∫ t in A i..B i, 1 / t| ≤
      (n : ℝ) * primeOrderedDiscrepancy R *
        (4 + primeOrderedDiscrepancy R) ^ (n - 1) := by
  rw [primeRectangle_factorization hR A B hA hB]
  have he := primeOrderedDiscrepancy_nonneg hR
  apply primeRectangle_product_difference n _ _ _ _ (by linarith) he
  · intro i
    rw [abs_of_nonneg (sum_nonneg (fun p _ => by positivity))]
    exact primeSlab_interval_mass hR hs (hA i) (hAB i) (hB i)
  · intro i
    have hi := primeOrdered_exponent_density_bounds (hA i) (hAB i) (hB i)
    rw [abs_of_nonneg hi.1]
    linarith [hi.2]
  · intro i
    exact primeOrdered_reciprocal_Icc_uniform_bound hR hs (hA i) (hAB i) (hB i)

/-- Empty density product and empty actual mass both equal one. -/
theorem primeRectangle_zero_discrepancy (R : ℝ) (A B : Fin 0 → ℝ) :
    (∏ i, ∫ t in A i..B i, 1 / t) = 1 ∧
      |primeRectangleMass R A B - ∏ i, ∫ t in A i..B i, 1 / t| = 0 := by
  simp [primeRectangle_zero]

end Wu2008DoubleSieve

