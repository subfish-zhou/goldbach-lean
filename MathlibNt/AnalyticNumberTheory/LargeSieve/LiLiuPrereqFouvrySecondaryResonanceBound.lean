import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonanceReindex

/-!
# Consuming the secondary r-mean on the original occupied carrier

Only nonnegative costs are enlarged to the actual dyadic `r` interval.
The signed coefficient weight remains an exact, `r`-independent factor.
The mean keeps the existing losses: the span is bounded by `GridUpper+1`,
and the gcd average extends to `(0,hi]`, rather than paying just the width.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wGramFouvryCost_nonneg {C : ℝ} (hC : 0 ≤ C)
    (ε : ℝ) (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (L : WGramLabel) :
    0 ≤ wGramFouvryCost ε C a R S M Z K j cap L := by
  unfold wGramFouvryCost
  positivity

/-- Explicit dyadic mean for a fixed seven-coordinate base. The lower
modulus uses `2^(j 3)` and the averaging cost uses `2^(j 3+1)-1`. -/
def wGramSecondaryDyadicMean (ε C : ℝ) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (j cap : Fin 5 → ℕ) (v : WGramSecondaryBase) : ℝ :=
  (C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (v.1 * 2 ^ j 3 * v.2.1.2.1 * v.2.2.2.1 : ℕ)) *
    (v.1 * (2 ^ (j 3 + 1) - 1) * v.2.1.2.1 * v.2.2.2.1 : ℕ) ^
      (1 / 2 + ε : ℝ)) *
  ((2 ^ (j 3 + 1) - 1 : ℕ) * Real.sqrt
    ((v.1 * v.2.2.2.1 * v.2.1.2.1 *
      (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a
        v.2.1.2.2).natAbs.divisors.card : ℕ) : ℝ))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
