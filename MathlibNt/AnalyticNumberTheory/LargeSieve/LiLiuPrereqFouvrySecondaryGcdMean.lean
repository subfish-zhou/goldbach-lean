import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonance
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Removing the artificial progression-step loss in the secondary mean

The previous inclusion of multiples in `(0,B*s]` paid a full factor `s`.
The gcd product inequality instead pays only `gcd(s,|A|)`. No coprimality
of `s` and `A`, and no nonzero coefficient of the common `n`, is assumed.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem gcd_mul_le_gcd_mul_gcd {A : ℕ} (hA : 0 < A) (r s : ℕ) :
    (r * s).gcd A ≤ s.gcd A * r.gcd A := by
  apply Nat.le_of_dvd
    (Nat.mul_pos (Nat.gcd_pos_of_pos_right s hA) (Nat.gcd_pos_of_pos_right r hA))
  simpa only [gcd_eq_nat_gcd, Nat.gcd_comm, Nat.mul_comm] using
    gcd_mul_dvd_mul_gcd A r s

theorem sum_gcd_multiples_le {A : ℕ} (hA : A ≠ 0) (s B : ℕ) :
    (∑ r ∈ Ioc 0 B, (r * s).gcd A) ≤
      B * (s.gcd A * A.divisors.card) := by
  calc
    _ ≤ ∑ r ∈ Ioc 0 B, s.gcd A * r.gcd A :=
      sum_le_sum (fun r _ => gcd_mul_le_gcd_mul_gcd (Nat.pos_of_ne_zero hA) r s)
    _ = s.gcd A * ∑ r ∈ Ioc 0 B, r.gcd A := (mul_sum _ _ _).symm
    _ ≤ s.gcd A * (B * A.divisors.card) := by
      apply Nat.mul_le_mul_left
      simpa only [Nat.gcd_comm] using sum_gcd_le hA B
    _ = _ := by ring

theorem iv3_secondary_gcd_sum_refined
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) (B : ℕ) :
    (∑ r ∈ Ioc 0 B, (n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs) ≤
      B * (n * s' *
        (s.gcd (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs *
          (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card)) := by
  simp_rw [iv3_secondary_gcd hsec]
  rw [← mul_sum]
  calc
    _ ≤ (n * s') * (B *
        (s.gcd (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs *
          (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card)) :=
      Nat.mul_le_mul_left _ (sum_gcd_multiples_le
        (Int.natAbs_ne_zero.mpr (iv3SecondaryNumerator_ne_zero hsec hl)) s B)
    _ = _ := by ring

theorem iv3_secondary_sqrt_gcd_sum_refined
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0) (B : ℕ) :
    (∑ r ∈ Ioc 0 B, Real.sqrt ((n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      B * Real.sqrt ((n * s' *
        (s.gcd (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs *
          (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card) : ℕ) : ℝ) := by
  let E := n * s' *
    (s.gcd (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs *
      (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card)
  have hm : (∑ r ∈ Ioc 0 B, ((n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      (B : ℝ) * E := by
    exact_mod_cast iv3_secondary_gcd_sum_refined hsec hl B
  calc
    _ ≤ Real.sqrt (B : ℝ) * Real.sqrt
        (∑ r ∈ Ioc 0 B, ((n * r * s * s').gcd
          (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) := by
      simpa using Real.sum_sqrt_mul_sqrt_le (f := fun _ : ℕ => (1 : ℝ))
        (g := fun r => ((n * r * s * s').gcd
          (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ))
        (Ioc 0 B) (fun _ => by positivity) (fun _ => by positivity)
    _ ≤ Real.sqrt (B : ℝ) * Real.sqrt ((B : ℝ) * E) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg B),
        show (B : ℝ) * ((B : ℝ) * E) = (B : ℝ) ^ 2 * E by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg B)]

/-- With a unit progression step modulo the numerator, the extra square-root
step cost vanishes completely. The general result does not require this case. -/
theorem iv3_secondary_sqrt_gcd_sum_coprime
    {d₁ n n₂ n₂' s s' : ℕ} {a h h' : ℤ}
    (hsec : h' * s = h * s')
    (hl : iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h' ≠ 0)
    (hsA : s.Coprime (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs) (B : ℕ) :
    (∑ r ∈ Ioc 0 B, Real.sqrt ((n * r * s * s').gcd
      (iv3CorrelationNumerator d₁ n n₂ n₂' s s' a h h').natAbs : ℝ)) ≤
      B * Real.sqrt ((n * s' *
        (iv3SecondaryNumerator d₁ n₂ n₂' a h).natAbs.divisors.card : ℕ) : ℝ) := by
  simpa only [hsA.gcd_eq_one, one_mul] using
    iv3_secondary_sqrt_gcd_sum_refined hsec hl B

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
