import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131TailDecay

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-!
# Section 10 DDE reduction for the Proposition 13.1 unit shift

This file deliberately stops the source boundary *before* Lemma 10.29.  The
remaining source input is the one-sided conclusion of Lemma 10.28: the
logarithmic slope of the decreasing common-majorant envelope is non-positive.
The unit-shift estimate and its two-step Section 13 consumer are proved below.
-/

/-- The Iwaniec pairing in §10, specialized to the coefficient `b = 1`. -/
noncomputable def section10Pairing
    (R r : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * r s * R s - ∫ t in s - 1..s, r (t + 1) * R t

/-- Minimal non-circular `DDE(2,1,β)` apparatus used at `κ = 1`.

The record contains the original and adjoint equations, positivity, and the
vanishing pairing.  It contains no adjacent-value estimate. -/
structure Section10DDEApparatus (R : ℝ → ℝ) (β : ℝ) where
  adjoint : ℝ → ℝ
  beta_ge_one : 1 ≤ β
  continuous : ContinuousOn R (Ioi (β - 1))
  positive : ∀ s, β - 1 < s → 0 < R s
  adjoint_positive : ∀ s, β ≤ s → 0 < adjoint s
  original_dde : ∀ s, β < s →
    HasDerivAt R (-(2 * R s + R (s - 1)) / s) s
  adjoint_dde : ∀ s, 0 < s →
    HasDerivAt (fun u => u * adjoint u)
      (2 * adjoint s + adjoint (s + 1)) s
  pairing_zero : ∀ s, β < s → section10Pairing R adjoint s = 0


/- Lemma 10.28 is the explicit source boundary of this reduction.  Callers
must supply an actual `Section10CommonMajorant`; it is not postulated here. -/


/- Equations (13.8)--(13.10) and Lemma 10.17 form the other explicit source
boundary.  Callers must supply an actual bridge for each sign. -/


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
