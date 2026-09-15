import MathlibNt.SieveTheory.LiLiuGoldbachBuchstab

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Weakly ordered double sum, with the diagonal retained. -/
noncomputable def goldbachV (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ s ∈ goldbachHalfOpenPrimes N z y,
    ∑ r ∈ (goldbachHalfOpenPrimes N z y).filter (fun r => r ≤ s),
      literalH A (N * r) (r * s) s

/-- Actual diagonal square contribution, not an assumed error bound. -/
noncomputable def goldbachQ (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ r ∈ goldbachHalfOpenPrimes N z y, literalH A N (r ^ 2) r

/-- Strict triples r<s<t. The sieve cutoff is the middle prime s. -/
noncomputable def goldbachWStrict (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ t ∈ goldbachHalfOpenPrimes N z y,
    ∑ r ∈ goldbachHalfOpenPrimes N z (t : ℝ),
      ∑ s ∈ (goldbachHalfOpenPrimes N (r : ℝ) (t : ℝ)).filter (fun s => r < s),
        literalH A (N * r) (r * s * t) s

/-- Middle part of S4: the smaller prime is strictly below y. -/
noncomputable def goldbachS5HalfOpen (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ rs ∈ (goldbachS4Pairs N z).filter
      (fun rs => (rs.1 : ℝ) < y ∧ y ≤ (rs.2 : ℝ)),
    literalH A (N * rs.1) (rs.1 * rs.2) rs.2

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig