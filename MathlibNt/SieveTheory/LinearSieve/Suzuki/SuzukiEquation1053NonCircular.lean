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

lemma explicitKappaOneAdjointPlus_dde (s : ℝ) :
    HasDerivAt (fun u => u * explicitKappaOneAdjointPlus u)
      (2 * explicitKappaOneAdjointPlus s + explicitKappaOneAdjointPlus (s + 1)) s := by
  have h := (hasDerivAt_id s).mul
    (((hasDerivAt_pow 2 s).sub ((hasDerivAt_id s).const_mul 2)).add_const (1 / 2))
  change HasDerivAt (id * fun u : ℝ => u ^ 2 - 2 * u + 1 / 2) _ s
  apply h.congr_deriv
  norm_num [explicitKappaOneAdjointPlus]
  ring

noncomputable def kappaOneLogSlope (s : ℝ) : ℝ :=
  4 * s / (2 * s ^ 2 - 1)

lemma kappaOne_adjoint_logSlope_exact {s : ℝ} (hs : 1 ≤ s) :
    (explicitKappaOneAdjointPlus (s + 1) + explicitKappaOneAdjointPlus (s + 2)) /
      ((s + 1) * explicitKappaOneAdjointPlus (s + 1)) = kappaOneLogSlope s := by
  have hs1 : s + 1 ≠ 0 := by linarith
  have hden : 2 * s ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg s]
  simp only [explicitKappaOneAdjointPlus, kappaOneLogSlope]
  field_simp [hs1, hden]
  ring

lemma kappaOne_logSlope_error {s : ℝ} (hs : 2 ≤ s) :
    |kappaOneLogSlope s - 2 / s| ≤ 2 / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  have hden0 : 0 < 2 * s ^ 2 - 1 := by nlinarith [sq_nonneg s]
  have heq : kappaOneLogSlope s - 2 / s = 2 / (s * (2 * s ^ 2 - 1)) := by
    dsimp [kappaOneLogSlope]
    rw [div_sub_div]
    · congr 1 <;> ring
    · nlinarith
    · exact ne_of_gt hs0
  rw [heq, abs_of_pos (div_pos (by norm_num) (mul_pos hs0 hden0))]
  apply (div_le_div_iff₀ (mul_pos hs0 hden0) (pow_pos hs0 3)).2
  nlinarith [sq_nonneg s]

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

lemma kappaOne_logSlope_deriv_error {s : ℝ} (hs : 2 ≤ s) :
    |-4 * (2 * s ^ 2 + 1) / (2 * s ^ 2 - 1) ^ 2 + 2 / s ^ 2| ≤ 4 / s ^ 4 := by
  have hs0 : 0 < s := by linarith
  have hden0 : 0 < 2 * s ^ 2 - 1 := by nlinarith [sq_nonneg s]
  have heq : -4 * (2 * s ^ 2 + 1) / (2 * s ^ 2 - 1) ^ 2 + 2 / s ^ 2 =
      -(12 * s ^ 2 - 2) / (s ^ 2 * (2 * s ^ 2 - 1) ^ 2) := by
    field_simp [ne_of_gt hs0, ne_of_gt hden0]
    ring
  rw [heq, abs_div, abs_neg,
    abs_of_pos (by nlinarith [sq_nonneg s] : 0 < 12 * s ^ 2 - 2)]
  rw [abs_of_pos (mul_pos (sq_pos_of_pos hs0) (sq_pos_of_pos hden0))]
  apply (div_le_div_iff₀
    (mul_pos (sq_pos_of_pos hs0) (sq_pos_of_pos hden0)) (pow_pos hs0 4)).2
  have hs2 : 4 ≤ s ^ 2 := by nlinarith
  have hp : 0 ≤ s ^ 2 * (s ^ 2 - 4) :=
    mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs2)
  nlinarith

/-- A stationary equality is exactly a zero derivative of the logarithmic
minus envelope.  This uses only the genuine DDE and positivity. -/
lemma stationary_candidate_is_logEnvelope_stationary
    {R ξ : ℝ → ℝ} {β c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hξ : Proposition1020Xi ξ)
    (hsβ : β < s)
    (hstat : normalizedMinusBase R ξ s = c) :
    HasDerivAt (logEnvelopeMinus R ξ c) 0 s := by
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith [h.beta_ge_one]) hsβ.le
  have hRs : 0 < R s := h.positive s (by linarith)
  have hd := lemma1028_logEnvelopeMinus_hasDerivAt hξ (c := c) hs0 hRs
    (h.original_dde s hsβ)
  apply hd.congr_deriv
  dsimp [normalizedMinusBase] at hstat
  linarith

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

/-- Non-circular endpoint reduction.  `hstrict` is a single scalar real
inequality, not a stationary-exclusion field or a same-typed certificate.
It is exactly the first still-unproved (10.53) remainder inequality: all terms
on its two sides are fixed by the genuine pairing data. -/
theorem stationary_candidate_impossible_of_strict_remainder_bound
    {R ξ : ℝ → ℝ} {β s₀ C c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (_hξ : Proposition1020Xi ξ)
    (hsβ : β < s) (hs2 : 2 ≤ s)
    (_hs₀ : s₀ ≤ s) (_hc : C ≤ c)
    (_hstat : normalizedMinusBase R ξ s = c)
    (hstrict :
      (∫ t in s - 1..s,
        envelopeMinus R ξ c t *
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) <
        s * explicitKappaOneAdjointPlus s * R s) : False := by
  have heq := explicit_pairing_weighted_identity h hadj hsβ hs2 (ξ := ξ) (c := c)
  linarith


end Section10Equation1053NonCircular
