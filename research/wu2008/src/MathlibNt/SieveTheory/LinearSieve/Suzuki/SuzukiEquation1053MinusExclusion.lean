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

/-- Exact version of the first line used in (10.47).  The paper next replaces
its adjoint quotient by `(λ-1)/s + O(1/s²)`. -/
lemma psiMinus_hasDerivAt
    {R ξ : ℝ → ℝ} {β c s : ℝ} (h : FirstCrossingDDEApparatus R β)
    (hξ : Proposition1020Xi ξ) (hs : 0 < s + 1)
    (hr : 0 < h.adjoint (s + 1)) :
    HasDerivAt (psiMinus h.adjoint ξ c)
      (ξ s - c -
        (h.adjoint (s + 1) + h.adjoint (s + 2)) /
          ((s + 1) * h.adjoint (s + 1))) s := by
  have hphase := (xiPhase_hasDerivAt hξ s).sub
    (by simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul c)
  have hlog := log_adjoint_shift_hasDerivAt h hs hr
  exact hphase.sub hlog

/-- A pointwise Taylor/secant estimate for the canonical phase on a unit
interval.  This is the part of (10.47) supplied solely by Proposition 10.20. -/
lemma canonicalXi_unit_secant
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ)
    {s t : ℝ} (hs : 3 ≤ s) (ht : t ∈ Icc (s - 1) s) :
    0 ≤ ξ s - ξ t ∧ ξ s - ξ t ≤ 2 * (s - t) := by
  have hlo : 2 ≤ t := by linarith [ht.1]
  exact ⟨proposition1020_secant_nonneg hξ hlo ht.2,
    proposition1020_oneSidedCommonMajorantSlope hξ hlo ht.2⟩

/-- Exact integration-by-parts identity underlying (10.53).  It deliberately
keeps the remainder integral explicit; bounding it is precisely where source
(10.41)--(10.42), (10.47)--(10.52), and the asymptotics of Proposition 10.20
enter. -/
theorem exp_neg_integral_by_parts
    {ψ p q : ℝ → ℝ} {a b : ℝ}
    (hψ : ∀ t ∈ uIcc a b, HasDerivAt ψ (p t) t)
    (hp : ∀ t ∈ uIcc a b, HasDerivAt p (q t) t)
    (hp0 : ∀ t ∈ uIcc a b, p t ≠ 0)
    (hmain : IntervalIntegrable (fun t => Real.exp (-ψ t)) volume a b)
    (hrem : IntervalIntegrable
      (fun t => Real.exp (-ψ t) * q t / (p t)^2) volume a b) :
    (∫ t in a..b, Real.exp (-ψ t)) =
      Real.exp (-ψ a) / p a - Real.exp (-ψ b) / p b -
        ∫ t in a..b, Real.exp (-ψ t) * q t / (p t)^2 := by
  let F : ℝ → ℝ := fun t => -(Real.exp (-ψ t) / p t)
  have hF : ∀ t ∈ uIcc a b,
      HasDerivAt F
        (Real.exp (-ψ t) + Real.exp (-ψ t) * q t / (p t)^2) t := by
    intro t ht
    have he : HasDerivAt (fun u : ℝ => Real.exp (-ψ u))
        (-p t * Real.exp (-ψ t)) t := by
      simpa only [Pi.neg_apply, mul_comm] using (hψ t ht).neg.exp
    have hd := (he.div (hp t ht) (hp0 t ht)).neg
    change HasDerivAt F _ t at hd
    apply hd.congr_deriv
    field_simp [hp0 t ht]
    ring
  have hsum : IntervalIntegrable
      (fun t => Real.exp (-ψ t) + Real.exp (-ψ t) * q t / (p t)^2)
      volume a b := hmain.add hrem
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hsum
  have hadd := intervalIntegral.integral_add hmain hrem
  dsimp [F] at hFTC
  rw [hadd] at hFTC
  linarith

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
