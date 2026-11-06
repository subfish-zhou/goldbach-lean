module

public import MathlibNt.SieveTheory.FiniteLabelCounting
public import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution
public import MathlibNt.SieveTheory.FiniteRealWindows
public import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindow
public import MathlibNt.SieveTheory.LiLiuGoldbachB10RosserFactor


@[expose] public section

open scoped BigOperators
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section


theorem goldbachG11Linked_upperRosserCertificate {N : ℕ} {Z Δ s : ℝ}
    (hZ : 2 ≤ Z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log Z) (hslo : 3/2 ≤ s) :
    LinearSieve.IsUpperRosserCertificate (goldbachB10ProdPrimes N Z) (Nat.floor Δ+1) := by
  exact goldbachProdPrimes_upperRosserCertificate hZ hΔ hs hslo


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig