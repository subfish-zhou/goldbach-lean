import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence


open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

set_option maxHeartbeats 1600000

/-!
# Lemma 14.4, Case I successor: real-`τ` / `Σ₂` frontier

This file keeps Suzuki's literal
`τ = max s ((1 - log 2 / log D)⁻¹)`.  In particular it does not use the
incorrect simplification `τ = s` to erase `Σ₂`.

The exact finite recurrence, the global-IH instantiation, the internal `Σ₀`
endpoint, the natural-ceiling `Σ₁₂` theorem, and Claim (14.13) all compile in
the current import cone.  The theorem below closes the elementary carrier
part of the genuine `Σ₂` dichotomy: the sum is either in the even, nonempty
narrow branch, or is literally zero.
-/

/-- The source correction occurring in the upper splitting point of (14.9). -/
noncomputable def lemma144RealTau (D : ℕ) (s : ℝ) : ℝ :=
  max s ((1 - Real.log 2 / Real.log (D : ℝ))⁻¹)


end MathlibNt.SieveTheory
