module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Tactic

/-!
# Elementary finite objects for Mertens' theorems

This file defines the finite set of primes at most `x`, its reciprocal sum,
and the corresponding Euler product.  It contains only elementary finite-sum,
finite-product, positivity, and local logarithm estimates; analytic asymptotic
results belong in later modules.
-/

@[expose] public section

namespace AnalyticNumberTheory.Mertens

open Finset Real

/-- The finite set of prime natural numbers at most `x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  x.primesLE

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simpa only [primesUpTo, and_comm] using (Nat.mem_primesLE (p := p) (n := x))

/-- The sets of primes up to `x` are nested as `x` increases. -/
theorem primesUpTo_mono {x y : ℕ} (hxy : x ≤ y) : primesUpTo x ⊆ primesUpTo y := by
  exact Nat.primesLE_mono hxy

theorem primesUpTo_eq_empty_of_le_one {x : ℕ} (hx : x ≤ 1) : primesUpTo x = ∅ := by
  ext p
  simp only [mem_primesUpTo, Finset.notMem_empty, iff_false]
  intro hp'
  have hp2 := hp'.1.two_le
  omega

/-- The finite reciprocal-prime sum `∑ p ≤ x, 1 / p`. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => 1 / (p : ℝ)

/-- The finite Euler product `∏ p ≤ x, (1 - 1 / p)`. -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  (primesUpTo x).prod fun p => 1 - 1 / (p : ℝ)


theorem primeReciprocalSum_nonneg (x : ℕ) : 0 ≤ primeReciprocalSum x := by
  unfold primeReciprocalSum
  exact Finset.sum_nonneg fun p _ => by positivity

/-- The reciprocal-prime sum is monotone in its cutoff. -/
theorem primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro x y hxy
  unfold primeReciprocalSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (primesUpTo_mono hxy) ?_
  intro p _ _
  positivity


/-- Every Euler factor indexed by a prime is strictly positive. -/
theorem primeFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp1)).mpr hp1)


theorem primeProduct_pos (x : ℕ) : 0 < primeProduct x := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp => primeFactor_pos (mem_primesUpTo.mp hp).1


/-- Taking logarithms converts the finite Euler product into a finite sum. -/
theorem log_primeProduct (x : ℕ) :
    log (primeProduct x) =
      (primesUpTo x).sum (fun p => log (1 - 1 / (p : ℝ))) := by
  unfold primeProduct
  rw [Real.log_prod]
  intro p hp
  exact (primeFactor_pos (mem_primesUpTo.mp hp).1).ne'

/-- For `0 < t ≤ 1/2`, the error after linearizing `log (1 - t)` is at most
`2 t²`. -/
theorem abs_log_one_sub_add_le {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have ht : |t| < 1 := by rw [abs_of_pos ht0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le ht 1
  rw [abs_of_pos ht0] at h
  have hlinear : |log (1 - t) + t| ≤ t ^ 2 / (1 - t) := by
    simpa [Finset.sum_range_one, add_comm] using h
  refine hlinear.trans ((div_le_iff₀ (by linarith : 0 < 1 - t)).mpr ?_)
  nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - 2 * t by linarith)]

/-- The local logarithmic correction for a prime Euler factor. -/
theorem abs_log_primeFactor_add_le {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  have ht0 : 0 < 1 / (p : ℝ) := by
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : 1 / (p : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp.two_le)
  simpa only [div_pow, one_pow, mul_one_div] using
    abs_log_one_sub_add_le ht0 htle

end AnalyticNumberTheory.Mertens
