import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeCutoffBoundary
import MathlibNt.SieveTheory.LiLiuGoldbachG11PiLiEndpoints

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- Geometric prime window, before imposing the output-prime condition. -/
noncomputable def goldbachG11LinkedPrimeWindow (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun r => r.Prime ∧
    goldbachG11PiLiLo N ε m < (r : ℝ) ∧ (r : ℝ) ≤ goldbachG11PiLiHi N m


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig