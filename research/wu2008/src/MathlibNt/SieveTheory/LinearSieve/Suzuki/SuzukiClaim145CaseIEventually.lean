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

/-- Eventual Case-I form of (14.18), with no Claim 14.6 premise.  All sieve
geometry and the dimension-one local Euler-product hypothesis remain explicit
at the final call site. -/
theorem lemma8_7_caseI_contraction_for_sufficiently_large_D
    {S : BoundingSieve} {H : Section13HatLayers}
    {β s τ σ K d Δ : ℝ} {N : ℕ}
    (hH : Section13HatContract H β)
    (hd : 0 ≤ d) (hΔlower : -1 < Δ) (hΔupper : Δ < 1)
    (hσ : ∀ sign : ErrorSign, β + sign.epsilon ≤ σ)
    (hcaseI : Claim14_5CaseI β N s σ)
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∃ D₀, 1 < D₀ ∧ ∀ D z v w : ℝ, D₀ ≤ D →
      2 ≤ z → 2 ≤ v → 2 ≤ w → w ≤ v → v ≤ z →
      z = D ^ (1 / s) → v = D ^ (1 / τ) → w = D ^ (1 / σ) →
      suzukiLemmaEightSevenPrimeSum S D w v z
          (qD H (ErrorSign.ofDepth N).opposite D d Δ) <
        (1 - 1 / σ) ^ (1 - Δ) * errorEnvelope H N D d s +
          (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ τ /
            Real.log w) * (τ / s) := by
  have hβs : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s := by
    rw [hH.betaHat_eq, epsilon_ofDepth_eq_mod_two]
    exact hcaseI.1
  have hs : 0 < s := by
    have heps : 0 ≤ (ErrorSign.ofDepth N).epsilon := by
      cases ErrorSign.ofDepth N <;> simp [ErrorSign.epsilon]
    rw [hH.betaHat_eq] at hβs
    linarith [hH.beta_gt_one]
  obtain ⟨D₁, hD₁, hlarge₁⟩ :=
    claim14_6_i_ii_for_sufficiently_large_D hH hd hΔlower hσ
  have hβτ : β + (ErrorSign.ofDepth N).epsilon ≤ τ := by
    simpa [hH.betaHat_eq] using hτ.le
  obtain ⟨D₂, hD₂, hlarge₂⟩ :=
    claim14_6_iii_for_sufficiently_large_D_no_extra_premise
      hH (ErrorSign.ofDepth N) hd hΔupper hβτ hτσ
  refine ⟨max D₁ D₂, hD₁.trans_le (le_max_left _ _), ?_⟩
  intro D z v w hD hz2 hv2 hw2 hwv hvz hz hv hw
  have hD₁D : D₁ ≤ D := (le_max_left D₁ D₂).trans hD
  have hD₂D : D₂ ≤ D := (le_max_right D₁ D₂).trans hD
  obtain ⟨hiβ, hii⟩ := hlarge₁ D hD₁D
  have hi : Claim14_6_MonotoneLambdaPremise H D d σ := by
    intro sign ε hε
    rw [hH.betaHat_eq]
    exact hiβ sign ε hε
  have hiiiτ := hlarge₂ D hD₂D
  exact lemma8_7_qD_of_claim14_6_i_ii_direct_iii
    hH (hD₁.trans_le hD₁D) hz2 hv2 hw2 hwv hvz hz hv hw
    hτ hβs hsτ hτσ hs hK hlocal hi hii hiiiτ


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
