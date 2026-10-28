import MathlibNt.SieveTheory.FiniteLabelCounting
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution
import MathlibNt.SieveTheory.FiniteRealWindows
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindow
import MathlibNt.SieveTheory.LiLiuGoldbachB10RosserFactor


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