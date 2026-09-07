import MathlibNt.Wu2004MeanValue.BalancedPrincipalSelected

/-!
# Actual prime-count centering in Wu (2004), equation (5.7)

Both discrepancies use the same actual AP count. The main term here is the
actual number of primes, not li. Their difference is the principal error
summed over the modulus-dependent coprime source set, before taking absolute
values. The balanced PNT estimate pays this filtered difference uniformly.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators

noncomputable section

def primeCenteredAPSum (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime d then f m *
    ((scaledPrimeCount ((m : ℝ) * r m) d b m : ℝ) -
      realPrimeCount (r m) / d.totient) else 0

theorem primeCenteredAPSum_eq_inverse (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hr : ∀ m ∈ S, 0 ≤ r m) :
    primeCenteredAPSum S f r d b =
      ∑ m ∈ S, if m.Coprime d then f m *
        ((AnalyticNumberTheory.Sieve.primesInAP ⌊r m⌋₊ d
            (AnalyticNumberTheory.Sieve.natInvMod d m * b % d) : ℝ) -
          realPrimeCount (r m) / d.totient) else 0 := by
  unfold primeCenteredAPSum
  apply sum_congr rfl
  intro m hm
  by_cases hmd : m.Coprime d
  · rw [if_pos hmd, if_pos hmd,
      scaledPrimeCount_eq_inverse _ _ _ _ (mul_nonneg (Nat.cast_nonneg _) (hr m hm))
        (hS m hm) hmd]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (hS m hm).ne'
    rw [mul_div_cancel_left₀ _ hm0]
  · simp only [if_neg hmd]

theorem primeCenteredAPSum_eq_actual_sub_principal
    (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ)
    (hS : ∀ m ∈ S, 0 < m) :
    primeCenteredAPSum S f r d b = actualAPSum S f r d b -
      (∑ m ∈ S.filter (fun m => m.Coprime d), f m * principalError (r m)) /
        d.totient := by
  simp only [primeCenteredAPSum, actualAPSum, sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  by_cases hmd : m.Coprime d
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (hS m hm).ne'
    simp only [if_pos hmd, ebar, principalError, mul_div_cancel_left₀ _ hm0]
    ring
  · simp only [if_neg hmd, zero_div, sub_zero]

/-- The two families may even be selected independently for each modulus.
The coprimality mask is kept inside the prime-error sum. -/
theorem primeCenteredAPSum_sub_actual_weighted (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ (Q : ℕ) (S : ℕ → Finset ℕ) (f r : ℕ → ℕ → ℝ) (b : ℕ → ℕ),
      (Q : ℝ) ≤ x →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 1 ≤ m ∧ (m : ℝ) ≤ x ^ (1 - eta)) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, |f d m| ≤ F) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 2 ≤ r d m ∧ (m : ℝ) * r d m ≤ x) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |primeCenteredAPSum (S d) (f d) (r d) d (b d) -
          actualAPSum (S d) (f d) (r d) d (b d)|) ≤ C * x / Real.log x ^ A := by
  obtain ⟨C, hC, x₀, hbound⟩ := balanced_principal_error_selected_weighted A eta F hA heta hF
  refine ⟨C, hC, x₀, ?_⟩
  intro x hx Q S f r b hQ hS hf hr
  have h := hbound x hx Q (fun d => (S d).filter (fun m => m.Coprime d)) f r hQ
    (fun d hd m hm => hS d hd m (mem_filter.mp hm).1)
    (fun d hd m hm => hf d hd m (mem_filter.mp hm).1)
    (fun d hd m hm => hr d hd m (mem_filter.mp hm).1)
  convert h using 1
  apply sum_congr rfl
  intro d hd
  rw [primeCenteredAPSum_eq_actual_sub_principal _ _ _ _ _
    (fun m hm => (hS d hd m hm).1)]
  rw [sub_sub_cancel_left, abs_neg, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (d.totient : ℝ) by positivity), mul_div_assoc]

/-- An unconditional transport with the actual li-centered discrepancy
still visible on the right. An AP producer, not this transport alone,
is required to deduce distribution. -/
theorem weighted_primeCenteredAPSum_le_actual_add (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ (Q : ℕ) (S : ℕ → Finset ℕ) (f r : ℕ → ℕ → ℝ) (b : ℕ → ℕ),
      (Q : ℝ) ≤ x →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 1 ≤ m ∧ (m : ℝ) ≤ x ^ (1 - eta)) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, |f d m| ≤ F) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 2 ≤ r d m ∧ (m : ℝ) * r d m ≤ x) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |primeCenteredAPSum (S d) (f d) (r d) d (b d)|) ≤
        (∑ d ∈ Icc 1 Q, wuModulusWeight d *
          |actualAPSum (S d) (f d) (r d) d (b d)|) + C * x / Real.log x ^ A := by
  obtain ⟨C, hC, x₀, hbound⟩ := primeCenteredAPSum_sub_actual_weighted A eta F hA heta hF
  refine ⟨C, hC, x₀, ?_⟩
  intro x hx Q S f r b hQ hS hf hr
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        (|actualAPSum (S d) (f d) (r d) d (b d)| +
          |primeCenteredAPSum (S d) (f d) (r d) d (b d) -
            actualAPSum (S d) (f d) (r d) d (b d)|) := by
      apply sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left _ (wuModulusWeight_nonneg d)
      simpa only [add_sub_cancel] using abs_add_le
        (actualAPSum (S d) (f d) (r d) d (b d))
        (primeCenteredAPSum (S d) (f d) (r d) d (b d) -
          actualAPSum (S d) (f d) (r d) d (b d))
    _ = (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum (S d) (f d) (r d) d (b d)|) +
        ∑ d ∈ Icc 1 Q, wuModulusWeight d *
          |primeCenteredAPSum (S d) (f d) (r d) d (b d) -
            actualAPSum (S d) (f d) (r d) d (b d)| := by
      simp only [mul_add, sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl (hbound x hx Q S f r b hQ hS hf hr)

end
end Wu2004MeanValue