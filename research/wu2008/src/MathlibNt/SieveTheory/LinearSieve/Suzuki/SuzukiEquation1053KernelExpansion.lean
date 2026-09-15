import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053NonCircular

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Equation (10.53): source-correct first-crossing reduction

This file corrects the endpoint orientation of the minus first-crossing window.
It proves the pairing-to-kernel inequality with the left endpoint `s-1`, and
records the unique earliest scalar inequality still needed for the strict
(10.56) contradiction.  No stationary exclusion or strict kernel bound is a
record field or theorem premise.
-/

namespace Section10Equation1053KernelExpansion

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053
open Section10Equation1053NonCircular

/-- The exact data supplied by a source-correct minus first crossing.  For a
decreasing preceding history the window maximum is at `s-1`, not at `s`. -/
structure MinusFirstCrossingCandidate (R ξ : ℝ → ℝ) (c : ℝ) where
  s : ℝ
  stationary : normalizedMinusBase R ξ s = c
  window_upper : ∀ t ∈ Icc (s - 1) s,
    envelopeMinus R ξ c t ≤ envelopeMinus R ξ c (s - 1)

/-- Explicit κ=1 adjoint positivity on the complete shifted unit window. -/
lemma explicit_adjoint_window_pos {s t : ℝ} (hs : 2 ≤ s)
    (ht : t ∈ Icc (s - 1) s) :
    0 < explicitKappaOneAdjointPlus (t + 1) :=
  explicitKappaOneAdjointPlus_pos (by linarith [ht.1])

/-- Source-correct normalized pairing step preceding (10.56).  Notice the
factor `W₋(s-1)` on the right. -/
theorem pairing_le_leftEndpoint_kernel
    {R ξ : ℝ → ℝ} {β c : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (w : MinusFirstCrossingCandidate R ξ c)
    (hβs : β < w.s) (hs2 : 2 ≤ w.s)
    (hprodInt : IntervalIntegrable
      (fun t => envelopeMinus R ξ c t *
        Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t))
      volume (w.s - 1) w.s)
    (hkernelInt : IntervalIntegrable
      (fun t => Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t))
      volume (w.s - 1) w.s) :
    w.s * explicitKappaOneAdjointPlus w.s * R w.s ≤
      envelopeMinus R ξ c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) := by
  have heq := explicit_pairing_weighted_identity h hadj hβs hs2
    (ξ := ξ) (c := c)
  rw [heq]
  calc
    (∫ t in w.s - 1..w.s,
        envelopeMinus R ξ c t *
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) ≤
      ∫ t in w.s - 1..w.s,
        envelopeMinus R ξ c (w.s - 1) *
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hprodInt
      · exact hkernelInt.const_mul _
      · intro t ht
        exact mul_le_mul_of_nonneg_right (w.window_upper t ht)
          (Real.exp_pos _).le
    _ = envelopeMinus R ξ c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) := by
      rw [intervalIntegral.integral_const_mul]

/-- The exact scalar ratio occurring after the source-correct pairing step.
At stationarity its prefactor is the `(10.45)` quantity
`A = ξ(s)-c-2/s`; proving this ratio `< 1` is precisely the first unresolved
scalar inequality.  It is declared as an object, not assumed by any record. -/
noncomputable def equation1056ScalarRatio
    (ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  (ξ s - c - 2 / s) *
    (∫ t in s - 1..s,
      Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) /
    Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c (s - 1))

/-- Unique earliest scalar frontier left by the source audit.  A complete
internalization of (10.47)--(10.53) must prove this at a sufficiently large
explicit `c` and cutoff, from canonical ξ bounds and the explicit rational
adjoint estimates. -/
def Equation1053EarliestScalarInequality (ξ : ℝ → ℝ) (c s : ℝ) : Prop :=
  equation1056ScalarRatio ξ c s < 1

/-- The explicit adjoint input to (10.47) is already internal: its shifted
logarithmic slope differs from `2/s` by at most `2/s³`. -/
theorem explicit_adjoint_1041 {s : ℝ} (hs : 2 ≤ s) :
    |kappaOneLogSlope s - 2 / s| ≤ 2 / s ^ 3 :=
  kappaOne_logSlope_error hs

/-- Likewise the differentiated rational bound used in (10.51). -/
theorem explicit_adjoint_1042 {s : ℝ} (hs : 2 ≤ s) :
    |-4 * (2 * s ^ 2 + 1) / (2 * s ^ 2 - 1) ^ 2 + 2 / s ^ 2| ≤
      4 / s ^ 4 :=
  kappaOne_logSlope_deriv_error hs


end Section10Equation1053KernelExpansion
