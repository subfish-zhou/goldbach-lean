import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim1413Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISuccessor

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option maxHeartbeats 1600000

/-! Natural-ceiling closure of the `Σ₁₂` input.  The finite sum itself, a
Claim-14.6 conclusion, and `mainSum` are never assumed. -/


noncomputable def sigma12ContractionMultiplier (σ Δ : ℝ) : ℝ :=
  (1 - 1 / σ) ^ (1 - Δ)

noncomputable def sigma12InheritedBudget
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C K d Δ s : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ) * errorEnvelope H N (D : ℝ) d s

noncomputable def sigma12EndpointRemainder
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C K d Δ s σ : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ) *
      ((6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s /
          Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))

/-- The source contraction has a canonical strict midpoint enlargement. -/
theorem exists_sigma12_sameC_strictFactor
    {σ Δ : ℝ} (hσ : 1 < σ) (hΔ : Δ < 1) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier σ Δ) / 2 ∧
      sigma12ContractionMultiplier σ Δ < q.ρ := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hbasepos : 0 < 1 - 1 / σ := sub_pos.mpr ((div_lt_one hσ0).2 hσ)
  have hbaselt : 1 - 1 / σ < 1 := by
    have : 0 < 1 / σ := one_div_pos.mpr hσ0
    linarith
  have hexp : 0 < 1 - Δ := sub_pos.mpr hΔ
  have ha0 : 0 ≤ sigma12ContractionMultiplier σ Δ := by
    exact Real.rpow_nonneg hbasepos.le _
  have ha1 : sigma12ContractionMultiplier σ Δ < 1 := by
    exact Real.rpow_lt_one hbasepos.le hbaselt hexp
  let q : Lemma144StrictFactor :=
    { ρ := (1 + sigma12ContractionMultiplier σ Δ) / 2
      nonneg := by linarith
      lt_one := by linarith }
  refine ⟨q, rfl, ?_⟩
  dsimp [q]
  linarith


end MathlibNt.SieveTheory
