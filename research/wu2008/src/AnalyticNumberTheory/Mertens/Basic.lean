import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Elementary finite objects for Mertens' theorems

This file defines the finite set of primes at most `x`, its reciprocal sum,
and the corresponding Euler product.  It contains only elementary finite-sum,
finite-product, positivity, and local logarithm estimates; analytic asymptotic
results belong in later modules.
-/

namespace AnalyticNumberTheory.Mertens

open Finset Real

/-- The finite set of prime natural numbers at most `x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simp [primesUpTo, and_comm]

/-- The sets of primes up to `x` are nested as `x` increases. -/
theorem primesUpTo_mono {x y : ℕ} (hxy : x ≤ y) : primesUpTo x ⊆ primesUpTo y := by
  intro p hp
  rw [mem_primesUpTo] at hp ⊢
  exact ⟨hp.1, hp.2.trans hxy⟩

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

/-- There are no reciprocal-prime terms below `2`. -/
theorem primeReciprocalSum_eq_zero_of_le_one {x : ℕ} (hx : x ≤ 1) :
    primeReciprocalSum x = 0 := by
  simp [primeReciprocalSum, primesUpTo_eq_empty_of_le_one hx]

@[simp]
theorem primeReciprocalSum_zero : primeReciprocalSum 0 = 0 :=
  primeReciprocalSum_eq_zero_of_le_one (by decide)

@[simp]
theorem primeReciprocalSum_one : primeReciprocalSum 1 = 0 :=
  primeReciprocalSum_eq_zero_of_le_one le_rfl

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

@[simp]
theorem primeProduct_zero : primeProduct 0 = 1 := by
  unfold primeProduct
  rw [primesUpTo_eq_empty_of_le_one (by omega)]
  simp

@[simp]
theorem primeProduct_one : primeProduct 1 = 1 := by
  unfold primeProduct
  rw [primesUpTo_eq_empty_of_le_one (by omega)]
  simp

/-- Every Euler factor indexed by a prime is strictly positive. -/
theorem primeFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp1)).mpr hp1)

/-- Every Euler factor indexed by a prime is at most one. -/
theorem primeFactor_le_one {p : ℕ} (_hp : p.Prime) :
    1 - 1 / (p : ℝ) ≤ 1 := by
  exact sub_le_self _ (by positivity)

theorem primeProduct_pos (x : ℕ) : 0 < primeProduct x := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp => primeFactor_pos (mem_primesUpTo.mp hp).1

theorem primeProduct_nonneg (x : ℕ) : 0 ≤ primeProduct x :=
  (primeProduct_pos x).le

theorem primeProduct_le_one (x : ℕ) : primeProduct x ≤ 1 := by
  unfold primeProduct
  refine Finset.prod_le_one ?_ ?_
  · intro p hp
    exact (primeFactor_pos (mem_primesUpTo.mp hp).1).le
  · intro p hp
    exact primeFactor_le_one (mem_primesUpTo.mp hp).1

/-- The finite Euler product is antitone in its cutoff. -/
theorem primeProduct_antitone : Antitone primeProduct := by
  intro x y hxy
  unfold primeProduct
  refine Finset.prod_le_prod_of_subset_of_le_one (primesUpTo_mono hxy) ?_ ?_
  · intro p hp
    exact (primeFactor_pos (mem_primesUpTo.mp hp).1).le
  · intro p hp _
    exact primeFactor_le_one (mem_primesUpTo.mp hp).1

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
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  have hub : log (1 - t) ≤ -t := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
    calc
      -t - 2 * t ^ 2 = -(t * (1 + 2 * t)) := by ring
      _ ≤ -(t / (1 - t)) := neg_le_neg hmul
      _ = 1 - (1 - t)⁻¹ := by field_simp [hne]; ring
      _ ≤ log (1 - t) := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_le]
  constructor <;> nlinarith

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
