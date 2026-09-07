import MathlibNt.SieveTheory.LiLiuGoldbachG67PaidLower

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original nested G6 labels are exactly the closed upper triangle. -/
theorem goldbachG6Pairs_eq_filter_product (N : ℕ) (z b : ℝ) :
    goldbachG6Pairs N z b =
      ((goldbachClosedPrimes N z b).product (goldbachClosedPrimes N z b)).filter
        (fun a => a.1 ≤ a.2) := by
  classical
  ext a
  rw [mem_goldbachG6Pairs_iff, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  constructor
  · rintro ⟨hs, hr⟩
    have hp := mem_goldbachClosedPrimes_iff.mp hr
    have hq := mem_goldbachClosedPrimes_iff.mp hs
    exact ⟨⟨mem_goldbachClosedPrimes_iff.mpr
      ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans hq.2.2.2⟩, hs⟩,
      by exact_mod_cast hp.2.2.2⟩
  · rintro ⟨⟨hr, hs⟩, hrs⟩
    have hp := mem_goldbachClosedPrimes_iff.mp hr
    exact ⟨hs, mem_goldbachClosedPrimes_iff.mpr
      ⟨hp.1, hp.2.1, hp.2.2.1, by exact_mod_cast hrs⟩⟩

/-- Square = twice the closed triangle minus its diagonal, for any symmetric kernel. -/
theorem symmetric_sum_triangle (S : Finset ℕ) (W : ℕ → ℕ → ℝ)
    (hW : ∀ r s, W r s = W s r) :
    2 * (∑ a ∈ (S.product S).filter (fun a => a.1 ≤ a.2), W a.1 a.2) =
      (∑ r ∈ S, ∑ s ∈ S, W r s) + ∑ r ∈ S, W r r := by
  classical
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  have hflip : (∑ r ∈ S, ∑ s ∈ S, if s ≤ r then W r s else 0) =
      ∑ r ∈ S, ∑ s ∈ S, if r ≤ s then W r s else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hW s r]
  have hp : ∀ r s : ℕ,
      (if r ≤ s then W r s else 0) + (if s ≤ r then W r s else 0) =
      W r s + (if s = r then W r r else 0) := by
    intro r s
    rcases lt_trichotomy r s with h | h | h
    · simp [Nat.le_of_lt h, Nat.not_le_of_gt h, ne_of_gt h]
    · subst s
      simp
    · simp [Nat.le_of_lt h, Nat.not_le_of_gt h, ne_of_lt h]
  have heq : (∑ r ∈ S, ∑ s ∈ S, if r ≤ s then W r s else 0) +
      (∑ r ∈ S, ∑ s ∈ S, if s ≤ r then W r s else 0) =
      (∑ r ∈ S, ∑ s ∈ S, W r s) + ∑ r ∈ S, W r r := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, hp, Finset.sum_add_distrib]
    simp
  rw [hflip] at heq
  linarith

/-- Exact square–triangle–diagonal identity on the original G6 labels. -/
theorem goldbachG6Pairs_symmetric_sum (N : ℕ) (z b : ℝ) (W : ℕ → ℕ → ℝ)
    (hW : ∀ r s, W r s = W s r) :
    2 * (∑ a ∈ goldbachG6Pairs N z b, W a.1 a.2) =
      (∑ r ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachClosedPrimes N z b, W r s) +
      ∑ r ∈ goldbachClosedPrimes N z b, W r r := by
  rw [goldbachG6Pairs_eq_filter_product]
  exact symmetric_sum_triangle (goldbachClosedPrimes N z b) W hW

/-- Only the diagonal must be nonnegative; off-diagonal weights may be signed. -/
theorem goldbachG6Pairs_half_square_le (N : ℕ) (z b : ℝ) (W : ℕ → ℕ → ℝ)
    (hW : ∀ r s, W r s = W s r)
    (hdiag : ∀ r ∈ goldbachClosedPrimes N z b, 0 ≤ W r r) :
    (1 / 2 : ℝ) * (∑ r ∈ goldbachClosedPrimes N z b,
      ∑ s ∈ goldbachClosedPrimes N z b, W r s) ≤
      ∑ a ∈ goldbachG6Pairs N z b, W a.1 a.2 := by
  have heq := goldbachG6Pairs_symmetric_sum N z b W hW
  have hd : 0 ≤ ∑ r ∈ goldbachClosedPrimes N z b, W r r :=
    Finset.sum_nonneg hdiag
  linarith

/-- Product-dependent weights are symmetric without any separability assumption. -/
theorem goldbachG6Pairs_product_sum (N : ℕ) (z b : ℝ) (h : ℕ → ℝ) :
    2 * (∑ a ∈ goldbachG6Pairs N z b, h (a.1 * a.2)) =
      (∑ r ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachClosedPrimes N z b, h (r * s)) +
      ∑ r ∈ goldbachClosedPrimes N z b, h (r ^ 2) := by
  simpa only [pow_two] using
    goldbachG6Pairs_symmetric_sum N z b (fun r s => h (r * s))
      (fun r s => congrArg h (Nat.mul_comm r s))

/-- A signed product kernel needs nonnegativity only at the square labels. -/
theorem goldbachG6Pairs_product_half_square_le (N : ℕ) (z b : ℝ) (h : ℕ → ℝ)
    (hdiag : ∀ r ∈ goldbachClosedPrimes N z b, 0 ≤ h (r ^ 2)) :
    (1 / 2 : ℝ) * (∑ r ∈ goldbachClosedPrimes N z b,
      ∑ s ∈ goldbachClosedPrimes N z b, h (r * s)) ≤
      ∑ a ∈ goldbachG6Pairs N z b, h (a.1 * a.2) := by
  apply goldbachG6Pairs_half_square_le N z b (fun r s => h (r * s))
    (fun r s => congrArg h (Nat.mul_comm r s))
  simpa only [pow_two] using hdiag

/-- The totient is evaluated at the full product, including the square diagonal.
The original closed-prime carrier, hence its coprimality screen, is unchanged. -/
theorem goldbachG6Pairs_totient_product_sum (N : ℕ) (z b : ℝ) (h : ℕ → ℝ) :
    2 * (∑ a ∈ goldbachG6Pairs N z b,
      h (a.1 * a.2) / (Nat.totient (a.1 * a.2) : ℝ)) =
      (∑ r ∈ goldbachClosedPrimes N z b,
        ∑ s ∈ goldbachClosedPrimes N z b, h (r * s) / (Nat.totient (r * s) : ℝ)) +
      ∑ r ∈ goldbachClosedPrimes N z b, h (r ^ 2) / (Nat.totient (r ^ 2) : ℝ) :=
  goldbachG6Pairs_product_sum N z b (fun m => h m / (Nat.totient m : ℝ))

/-- No off-diagonal sign condition or false totient factorization is needed. -/
theorem goldbachG6Pairs_totient_product_half_square_le (N : ℕ) (z b : ℝ) (h : ℕ → ℝ)
    (hdiag : ∀ r ∈ goldbachClosedPrimes N z b, 0 ≤ h (r ^ 2)) :
    (1 / 2 : ℝ) * (∑ r ∈ goldbachClosedPrimes N z b,
      ∑ s ∈ goldbachClosedPrimes N z b, h (r * s) / (Nat.totient (r * s) : ℝ)) ≤
      ∑ a ∈ goldbachG6Pairs N z b,
        h (a.1 * a.2) / (Nat.totient (a.1 * a.2) : ℝ) := by
  apply goldbachG6Pairs_product_half_square_le N z b (fun m => h m / (Nat.totient m : ℝ))
  intro r hr
  exact div_nonneg (hdiag r hr) (Nat.cast_nonneg _)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
