import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053MinusExclusion

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Non-circular audit of the κ = 1 stationary-exclusion step

This file deliberately does **not** import or reproduce
`Equation1053RemainderCertificate`.  It proves the explicit-adjoint rational
identities and reduces a stationary candidate to the one strict real integral
inequality that the current hypotheses still do not prove.

The reduction also exposes an interface mismatch: the first-crossing argument
in `C2Lemma1028FirstCrossing433` produces only the equality
`normalizedMinusBase R ξ s = c`.  The usual proof of (10.53), however, first
uses that the weighted envelope on `[s-1,s]` is bounded by its value at `s`.
That window-maximum fact is not a consequence of the bare equality and is not
present in `Equation1053MinusExclusion`'s premises.
-/

namespace Section10Equation1053NonCircular

set_option autoImplicit false
set_option maxHeartbeats 800000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053

noncomputable def explicitKappaOneAdjointPlus (s : ℝ) : ℝ :=
  s ^ 2 - 2 * s + 1 / 2

lemma explicitKappaOneAdjointPlus_pos {s : ℝ} (hs : 2 ≤ s) :
    0 < explicitKappaOneAdjointPlus s := by
  dsimp [explicitKappaOneAdjointPlus]
  nlinarith [sq_nonneg (s - 1)]


noncomputable def kappaOneLogSlope (s : ℝ) : ℝ :=
  4 * s / (2 * s ^ 2 - 1)


lemma kappaOneLogSlope_hasDerivAt {s : ℝ} (hs : 1 ≤ s) :
    HasDerivAt kappaOneLogSlope
      (-4 * (2 * s ^ 2 + 1) / (2 * s ^ 2 - 1) ^ 2) s := by
  have hden : 2 * s ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg s]
  have hnum : HasDerivAt (fun u : ℝ => 4 * u) 4 s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul 4
  have hden' : HasDerivAt (fun u : ℝ => 2 * u ^ 2 - 1) (4 * s) s := by
    exact (((hasDerivAt_pow 2 s).const_mul 2).sub_const 1).congr_deriv (by norm_num; ring)
  have h := hnum.div hden' hden
  change HasDerivAt ((fun u : ℝ => 4 * u) / fun u => 2 * u ^ 2 - 1) _ s
  apply h.congr_deriv
  field_simp [hden]
  ring


/-- The exact pairing equality in the explicit κ=1 weighted variables. -/
lemma explicit_pairing_weighted_identity
    {R ξ : ℝ → ℝ} {β c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (hsβ : β < s) (hs2 : 2 ≤ s) :
    s * explicitKappaOneAdjointPlus s * R s =
      ∫ t in s - 1..s,
        envelopeMinus R ξ c t *
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t) := by
  have hr : ∀ t ∈ Icc (s - 1) s, 0 < h.adjoint (t + 1) := by
    intro t ht
    rw [hadj]
    exact explicitKappaOneAdjointPlus_pos (by linarith [ht.1])
  have hp := pairing_zero_weighted_identity h (ξ := ξ) (c := c) hsβ hr
  rw [hadj] at hp
  exact hp


end Section10Equation1053NonCircular
