import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution
open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve AnalyticNumberTheory.Sieve

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


theorem goldbachG11LinkedLevel_le {N Q : ℕ} {B : ℝ}
    (hN : 2 ≤ N) (hB : 0 < B) (hl : 1 ≤ Real.log (N : ℝ))
    (hQ : (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B) : Q ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hs : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N : ℝ)]
  have hr : (Q : ℝ) ≤ N :=
    hQ.trans ((div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hl hB.le)).trans hs)
  exact_mod_cast hr


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig