import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiErrorEnvelopeCeilBridge

open scoped Classical BigOperators Interval
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Honest algebraic absorption of the Case-II endpoint error.

The raw endpoint estimate has three pieces after transport from the cubic
endpoint: the Claim-14.6(iii) integral, the explicit qD/dimension-one endpoint,
and the Sigma11 plus Euler-product-ratio excesses.  Claim 14.6(iii) controls the
integral at `lambda ... 3`; the separate hypothesis `hLambda3` is intentionally
visible because Claim 14.6(i) is only stated on `[betaHat+epsilon, sigma]` and,
at odd depth with `betaHat=2`, does not compare a Case-II point `s<3` with `3`.
Likewise the two explicit endpoint bounds are kept as exact premises; proving
them may require a distinct large-D inequality.

This theorem is arranged in the scale used by Claim 14.5: `outer * logScale *
errorEnvelope`.  It is directly reusable after instantiating `outer` with the
Euler-product/exponential prefactor and `logScale` with `(log D)^(-Delta)`. -/
theorem caseII_explicit_endpoint_error_absorb
    {H : Section13HatLayers} {N : ℕ}
    {D d Δ σ s outer logScale mainTerm total
      qEndpoint sigma11Endpoint ratioExcess
      qCoeff sigma11Coeff ratioCoeff : ℝ}
    (hs : 0 < s)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hOuter : 0 ≤ outer) (hLogScale : 0 ≤ logScale)
    (hiii :
      (∫ t in (3 : ℝ)..σ,
          qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
        (1 - 1 / σ) ^ (1 - Δ) *
          lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hLambda3 :
      lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
        lambda H (ErrorSign.ofDepth N) D d 0 s)
    (hqEndpoint : qEndpoint ≤
      qCoeff * errorEnvelope H N D d s)
    (hSigma11 : sigma11Endpoint ≤
      outer * logScale *
        (sigma11Coeff * errorEnvelope H N D d s))
    (hRatio : ratioExcess ≤
      outer * logScale *
        (ratioCoeff * errorEnvelope H N D d s))
    (hraw : total ≤
      mainTerm +
        outer * logScale *
          ((1 / s) * (∫ t in (3 : ℝ)..σ,
            qD H (ErrorSign.ofDepth N).opposite D d Δ t) + qEndpoint) +
        sigma11Endpoint + ratioExcess) :
    total ≤
      mainTerm + outer * logScale *
        (((1 - 1 / σ) ^ (1 - Δ) + qCoeff +
            sigma11Coeff + ratioCoeff) *
          errorEnvelope H N D d s) := by
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  let E : ℝ := errorEnvelope H N D d s
  let I : ℝ := ∫ t in (3 : ℝ)..σ,
    qD H (ErrorSign.ofDepth N).opposite D d Δ t
  have hLambda : c * lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      c * lambda H (ErrorSign.ofDepth N) D d 0 s :=
    mul_le_mul_of_nonneg_left hLambda3 hcut
  have hI : I ≤ c * lambda H (ErrorSign.ofDepth N) D d 0 s :=
    hiii.trans hLambda
  have hsInv : 0 ≤ 1 / s := (one_div_pos.mpr hs).le
  have hscaled := mul_le_mul_of_nonneg_left hI hsInv
  have hscaledE : (1 / s) * I ≤ c * E := by
    calc
      (1 / s) * I ≤ (1 / s) *
          (c * lambda H (ErrorSign.ofDepth N) D d 0 s) := hscaled
      _ = c * E := by
        dsimp [E]
        rw [errorEnvelope_eq_lambda_div H hs]
        ring
  have hmiddle : (1 / s) * I + qEndpoint ≤
      (c + qCoeff) * E := by
    calc
      (1 / s) * I + qEndpoint ≤ c * E + qCoeff * E :=
        add_le_add hscaledE hqEndpoint
      _ = (c + qCoeff) * E := by ring
  have hOuterLog : 0 ≤ outer * logScale := mul_nonneg hOuter hLogScale
  have hmiddleScaled := mul_le_mul_of_nonneg_left hmiddle hOuterLog
  calc
    total ≤ mainTerm + outer * logScale * ((1 / s) * I + qEndpoint) +
        sigma11Endpoint + ratioExcess := hraw
    _ ≤ mainTerm + outer * logScale * ((c + qCoeff) * E) +
        (outer * logScale * (sigma11Coeff * E)) +
        (outer * logScale * (ratioCoeff * E)) := by
      gcongr
    _ = mainTerm + outer * logScale *
        ((c + qCoeff + sigma11Coeff + ratioCoeff) * E) := by ring

/-- A convenient version in which the three non-integral explicit errors are
bounded together.  This is the maximal honest endpoint theorem when the
product-ratio and Sigma11 estimates are available only as one eventual
large-D packet. -/
theorem caseII_explicit_endpoint_error_absorb_packet
    {H : Section13HatLayers} {N : ℕ}
    {D d Δ σ s outer logScale mainTerm total explicitEndpoint endpointCoeff : ℝ}
    (hs : 0 < s)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hOuter : 0 ≤ outer) (hLogScale : 0 ≤ logScale)
    (hiii :
      (∫ t in (3 : ℝ)..σ,
          qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
        (1 - 1 / σ) ^ (1 - Δ) *
          lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hLambda3 :
      lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
        lambda H (ErrorSign.ofDepth N) D d 0 s)
    (hexplicit : explicitEndpoint ≤
      outer * logScale *
        (endpointCoeff * errorEnvelope H N D d s))
    (hraw : total ≤ mainTerm +
      outer * logScale *
        ((1 / s) * (∫ t in (3 : ℝ)..σ,
          qD H (ErrorSign.ofDepth N).opposite D d Δ t)) +
      explicitEndpoint) :
    total ≤ mainTerm + outer * logScale *
      (((1 - 1 / σ) ^ (1 - Δ) + endpointCoeff) *
        errorEnvelope H N D d s) := by
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  let E : ℝ := errorEnvelope H N D d s
  let I : ℝ := ∫ t in (3 : ℝ)..σ,
    qD H (ErrorSign.ofDepth N).opposite D d Δ t
  have hLambda : c * lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      c * lambda H (ErrorSign.ofDepth N) D d 0 s :=
    mul_le_mul_of_nonneg_left hLambda3 hcut
  have hI : I ≤ c * lambda H (ErrorSign.ofDepth N) D d 0 s :=
    hiii.trans hLambda
  have hscaled := mul_le_mul_of_nonneg_left hI (one_div_pos.mpr hs).le
  have hscaledE : (1 / s) * I ≤ c * E := by
    calc
      (1 / s) * I ≤ (1 / s) *
          (c * lambda H (ErrorSign.ofDepth N) D d 0 s) := hscaled
      _ = c * E := by
        dsimp [E]
        rw [errorEnvelope_eq_lambda_div H hs]
        ring
  have hOuterLog : 0 ≤ outer * logScale := mul_nonneg hOuter hLogScale
  have hm := mul_le_mul_of_nonneg_left hscaledE hOuterLog
  calc
    total ≤ mainTerm + outer * logScale * ((1 / s) * I) + explicitEndpoint := hraw
    _ ≤ mainTerm + outer * logScale * (c * E) +
        outer * logScale * (endpointCoeff * E) :=
      by gcongr
    _ = mainTerm + outer * logScale * ((c + endpointCoeff) * E) := by ring


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
