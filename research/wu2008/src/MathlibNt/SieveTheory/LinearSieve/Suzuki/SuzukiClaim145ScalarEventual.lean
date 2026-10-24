import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseBAllS

open scoped Classical BigOperators
open Filter Finset Topology
open Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- At Suzuki's exact moving endpoint, both analytic premises required by the
internal Claim-14.5 comparison hold eventually. -/
theorem claim145_sourceSigma_scalar_eventually
    (S : BoundingSieve) {d Δ K C C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ᶠ D : ℝ in atTop,
      Real.exp 1 * suzukiSourceL D K ≤ sourceSigma D d - 2 ∧
      Real.exp
          (suzukiSourceL D K +
            (sourceSigma D d - 2) *
              (1 + Real.log (suzukiSourceL D K) -
                Real.log (sourceSigma D d - 2))) ≤
        C145 *
          (claim14_5VProduct S D *
            (Real.exp (Real.sqrt K) /
              (Real.log D * sourceSigma D d)) *
            ((1 + (sourceSigma D d) ^ d / Real.log D) ^
                (sourceSigma D d) * sourceSigma D d *
              proposition131iiLowerProfile C (sourceSigma D d)) *
            (Real.log D) ^ (-Δ)) := by
  -- Specialize the uniform Case-B estimate to its own moving endpoint.
  filter_upwards [claim145_sourceSigma_allS_scalar_eventually
    (C := C) (M := (0 : ℝ)) S hΔ0 hΔ1 hd hK hC145 hlocal] with D hD
  exact (hD (sourceSigma D d) le_rfl).2.2

end MathlibNt.SieveTheory
