import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028CommonMajorant
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028FirstCrossing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Equation1053

set_option autoImplicit false
set_option maxHeartbeats 800000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing


/-!
# The analytic core preceding Suzuki (10.53)

This file internalizes the exact calculus and pairing identities used before the
asymptotic estimates in (10.47)--(10.53).  No derivative sign, adjacent-value
estimate, or `Equation1053MinusExclusion` is assumed.
-/

/-- The phase `φ₋(s)=∫₁ˢ ξ(t)dt-cs`. -/
noncomputable def phiMinus (ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  xiPhase ξ s - c * s

/-- The exponent `ψ₋(s)=φ₋(s)-log r(s+1)` in (10.46)--(10.53). -/
noncomputable def psiMinus (r ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  phiMinus ξ c s - Real.log (r (s + 1))

/-- Weighted minus envelope, in a form convenient for the pairing identity. -/
noncomputable def envelopeMinus (R ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  R s * Real.exp (phiMinus ξ c s)

@[simp] lemma exp_neg_psiMinus
    {r ξ : ℝ → ℝ} {c t : ℝ} (hr : 0 < r (t + 1)) :
    Real.exp (-psiMinus r ξ c t) =
      r (t + 1) * Real.exp (-phiMinus ξ c t) := by
  rw [psiMinus, neg_sub, Real.exp_sub, Real.exp_log hr]
  rw [Real.exp_neg]
  rfl

/-- The adjoint equation alone gives the exact first derivative of `r`.
For `a=2,b=1` this is the non-asymptotic precursor of source (10.41). -/
lemma adjoint_hasDerivAt
    {R : ℝ → ℝ} {β : ℝ} (h : FirstCrossingDDEApparatus R β)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt h.adjoint ((h.adjoint s + h.adjoint (s + 1)) / s) s := by
  have hprod := h.adjoint_dde s hs
  have hquot := hprod.div (hasDerivAt_id s) (ne_of_gt hs)
  have heq : ((fun u : ℝ => u * h.adjoint u) / id) =ᶠ[𝓝 s] h.adjoint := by
    filter_upwards [eventually_ne_nhds (ne_of_gt hs)] with u hu
    simp [hu]
  have hh := hquot.congr_of_eventuallyEq heq.symm
  apply hh.congr_deriv
  simp only [id_eq]
  field_simp [ne_of_gt hs]
  ring

/-- Exact derivative of `log r(s+1)`, before the asymptotic replacement (10.41). -/
lemma log_adjoint_shift_hasDerivAt
    {R : ℝ → ℝ} {β : ℝ} (h : FirstCrossingDDEApparatus R β)
    {s : ℝ} (hs : 0 < s + 1) (hr : 0 < h.adjoint (s + 1)) :
    HasDerivAt (fun t : ℝ => Real.log (h.adjoint (t + 1)))
      ((h.adjoint (s + 1) + h.adjoint (s + 2)) /
        ((s + 1) * h.adjoint (s + 1))) s := by
  have hadj := (adjoint_hasDerivAt h hs).comp s ((hasDerivAt_id s).add_const 1)
  have hlog := hadj.log (ne_of_gt hr)
  have hcoef :
      (h.adjoint (s + 1) + h.adjoint (s + 1 + 1)) / (s + 1) * 1 /
          h.adjoint (s + 1) =
        (h.adjoint (s + 1) + h.adjoint (s + 2)) /
          ((s + 1) * h.adjoint (s + 1)) := by
    field_simp [ne_of_gt hs, ne_of_gt hr]
    ring
  have hh := hlog.congr_deriv hcoef
  simpa only [Function.comp_apply, id_eq] using hh




/-- Pairing-zero rewritten in the weighted variables used in (10.54), with no
monotonicity hypothesis. -/
theorem pairing_zero_weighted_identity
    {R ξ : ℝ → ℝ} {β c s : ℝ} (h : FirstCrossingDDEApparatus R β)
    (hs : β < s)
    (hr : ∀ t ∈ Icc (s - 1) s, 0 < h.adjoint (t + 1)) :
    s * h.adjoint s * R s =
      ∫ t in s - 1..s,
        envelopeMinus R ξ c t * Real.exp (-psiMinus h.adjoint ξ c t) := by
  rw [h.pairing_zero s hs]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (s - 1) s := by
    simpa [uIcc_of_le (by linarith : s - 1 ≤ s)] using ht
  change h.adjoint (t + 1) * R t =
    envelopeMinus R ξ c t * Real.exp (-psiMinus h.adjoint ξ c t)
  rw [exp_neg_psiMinus (hr t ht')]
  dsimp [envelopeMinus]
  have hexp : Real.exp (phiMinus ξ c t) * Real.exp (-phiMinus ξ c t) = 1 := by
    rw [← Real.exp_add]
    simp
  symm
  calc
    R t * Real.exp (phiMinus ξ c t) *
        (h.adjoint (t + 1) * Real.exp (-phiMinus ξ c t)) =
      h.adjoint (t + 1) * R t *
        (Real.exp (phiMinus ξ c t) * Real.exp (-phiMinus ξ c t)) := by ring
    _ = h.adjoint (t + 1) * R t := by rw [hexp, mul_one]

/- The requested stationary exclusion cannot yet be derived from
`FirstCrossingDDEApparatus`: source (10.47) already invokes the asymptotic
`(log r(s+1))'=(λ-1)/s+O(1/s²)`, while the apparatus records only its exact
adjoint DDE.  The theorem above therefore marks the strongest source-faithful
boundary without adding (10.53), a derivative sign, or an adjacent-value
estimate as a premise. -/


end Section10Equation1053
