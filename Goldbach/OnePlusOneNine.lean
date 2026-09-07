import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorQuantitative

/-!
# Li–Liu's one-plus-one-point-nine theorem

This entry point exposes the unconditional existence theorem and the quantitative
bound for distinct primes. `Goldbach.Theorem` remains the independent Chen 1+2
entry point. Import `Goldbach.All` to use both public interfaces together.
-/

namespace Goldbach

/-- Every sufficiently large even integer has the Li–Liu representation,
with its exponent restriction written using exact natural powers. -/
theorem one_plus_one_nine :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ r ^ 10 ≤ q ^ 9 :=
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_onePlusOneNine_nat_unconditional

/-- The same existence theorem in the paper's real-exponent notation. -/
theorem one_plus_one_nine_real :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ ((19 / 10 : ℝ) - 1) :=
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_onePlusOneNine_unconditional

/-- The strict paper bound counts distinct primes p, using the Liu singular series. -/
theorem one_plus_one_nine_count :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (1 / 2500 : ℝ) *
        (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ 2) <
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19 N : ℝ) :=
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_D19_gt_paper_0004

/-- Fix the coefficient before choosing the common eventual threshold. -/
theorem one_plus_one_nine_lower_bound (κ : ℝ)
    (hκ : κ < (515093 / 800000000 : ℝ)) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      κ * (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log (N : ℝ) ^ 2) ≤
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19 N : ℝ) :=
  MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_D19_author_lower_of_coefficient_lt κ hκ

end Goldbach
