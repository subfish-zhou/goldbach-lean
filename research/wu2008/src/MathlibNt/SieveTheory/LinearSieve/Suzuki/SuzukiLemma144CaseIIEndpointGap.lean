import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddSuccessorSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceSigmaFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Case-II odd recursive endpoint: exact remaining scaling bridge

The accepted source-`σ` Claim 14.5 controls the recombined recursive endpoint
at the scale

`C145 * V(D) * exp(sqrt K) / (log D * sourceSigma D d)
      * E_N(D, sourceSigma D d) * (log D)^(-Δ)`.

The same-`C` endpoint-gap normalization instead requires this to fit below

`V(⌈D^(1/s)⌉) * C * exp(sqrt K) * E_N(D,s) * (log D)^(-Δ)
      * (1 - caseIIConcreteRoundedRelativeBracket ...)`.

The theorem below consumes Claim 14.5 and isolates exactly that comparison.  In
particular, a bare proof that the bracket is `< 1` supplies only positivity of
the last factor and does not supply the quantitative lower bound needed to
compare the two displayed scales uniformly in `s`.
-/

/-- The literal endpoint to which the accepted source-`σ` Claim 14.5 applies. -/
noncomputable def caseIIOddClaim145Endpoint
    (S : BoundingSieve) (d : ℝ) (N D : ℕ) : ℝ :=
  suzukiActualT S N D
    ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊

/-- The exact, expanded scale comparison still needed after applying the
accepted source-`σ` Claim 14.5.  The threshold is before `s`, as required by the
odd endpoint normalization. -/
def Lemma144CaseIIOddClaim145ScalingBridge
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C K C145 : ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 3 ≤ N →
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        C145 * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) ≤
          suzukiVProduct S
              (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
            ((C * Real.exp (Real.sqrt K) *
                errorEnvelope H N (D : ℝ) d s *
                (Real.log (D : ℝ)) ^ (-Δ)) *
              (1 - caseIIConcreteRoundedRelativeBracket N (D : ℝ) d Δ
                (sourceSigma (D : ℝ) d) C K))

/-- A strict bracket inequality alone is quantitatively insufficient for endpoint
absorption: even with positive endpoint and budget scales there are brackets
strictly below one whose gap is too small. -/
theorem strict_bracket_lt_one_does_not_force_endpoint_absorption
    {endpoint budget : ℝ} (he : 0 < endpoint) (hb : 0 < budget) :
    ∃ bracket : ℝ, bracket < 1 ∧
      ¬ endpoint ≤ budget * (1 - bracket) := by
  refine ⟨1 - endpoint / (2 * budget), ?_, ?_⟩
  · have : 0 < endpoint / (2 * budget) := by positivity
    linarith
  · have hne : budget ≠ 0 := ne_of_gt hb
    rw [show budget * (1 - (1 - endpoint / (2 * budget))) = endpoint / 2 by
      field_simp [hne]
      ring]
    linarith

/-- Claim 14.5 closes the recursive endpoint-gap normalization exactly when the
remaining scale bridge is supplied.  No enlargement of the target constant
`C` occurs. -/
theorem lemma144_caseII_odd_endpoint_gap_of_claim145_scaling_bridge
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C K C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H)
    (hscale : Lemma144CaseIIOddClaim145ScalingBridge S H d Δ C K C145) :
    Lemma144CaseIIOddEndpointGapNormalization S H
      (caseIIOddClaim145Endpoint S d) d Δ C K := by
  obtain ⟨Dc, hDc1, hc⟩ :=
    claim145_sourceSigma_endpoint_internal S H hΔ0 hΔ1 hd hK hC145
      hlocal hH
  intro N hN hN3
  obtain ⟨Ds, hDs1, hs⟩ := hscale N hN hN3
  refine ⟨max Dc Ds, hDc1.trans_le (le_max_left _ _), ?_⟩
  intro D hD s hs1 hs3
  have hDcD : Dc ≤ (D : ℝ) := (le_max_left Dc Ds).trans hD
  have hDsD : Ds ≤ (D : ℝ) := (le_max_right Dc Ds).trans hD
  exact (hc D N hDcD).trans (hs D hDsD s hs1 hs3)


end MathlibNt.SieveTheory
