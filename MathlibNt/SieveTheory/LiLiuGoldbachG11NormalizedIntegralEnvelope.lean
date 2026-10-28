import MathlibNt.SieveTheory.Arithmetic.LiuLogScaleAbsorption
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG11EulerFactorNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG11RemainderPayments

open Filter Set LiLiuPrereqBuchstab
open scoped Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Scalar log payment, reusing the proof of the private B8 normalized-main-mass helper.
No new analytic input: only divergence of log and the universal singular-series floor. -/
theorem goldbachG11NormalizedIntegral_logError_paid (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  simpa only [Real.rpow_ofNat, mul_assoc, mul_div_assoc] using
    (MathlibNt.SieveTheory.LiuWeight.eventually_inverse_log_remainder_le_liuSingularSeries
      C δ hδ)


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig