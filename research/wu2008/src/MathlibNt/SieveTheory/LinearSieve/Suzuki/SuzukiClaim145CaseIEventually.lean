import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146LargePackage
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146IntegralClosure

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

private lemma epsilon_ofDepth_eq_mod_two (N : ℕ) :
    (ErrorSign.ofDepth N).epsilon = (N % 2 : ℕ) := by
  rcases Nat.even_or_odd N with hN | hN
  · rw [ErrorSign.ofDepth_of_even hN, Nat.even_iff.mp hN]
    norm_num [ErrorSign.epsilon]
  · rw [ErrorSign.ofDepth_of_odd hN, Nat.odd_iff.mp hN]
    norm_num [ErrorSign.epsilon]

/-- The finite (14.18) assembly with Claim 14.6(iii) supplied only at the
actual Case-I lower endpoint `τ`.  This is the pointwise interface needed to
combine the independently eventual forms of Claims 14.6(i)--(iii). -/
theorem lemma8_7_qD_of_claim14_6_i_ii_direct_iii
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} {N : ℕ}
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
    (hβs : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s)
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hs : 0 < s) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hi : Claim14_6_MonotoneLambdaPremise H D d σ)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ)
    (hiiiτ : (∫ t in τ..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t) <
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) D d 0 τ) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (qD H (ErrorSign.ofDepth N).opposite D d Δ) <
      (1 - 1 / σ) ^ (1 - Δ) * errorEnvelope H N D d s +
        (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ τ /
          Real.log w) * (τ / s) := by
  exact lemma8_7_qD_of_claim14_6_i_ii_iii
    hH hD hz2 hv2 hw2 hwv hvz hz hv hw
    hτ hβs hsτ hτσ hs hK hlocal hi hii hiiiτ



end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
