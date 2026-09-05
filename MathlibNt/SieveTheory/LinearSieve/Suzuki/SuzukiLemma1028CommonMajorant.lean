import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1028

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The κ = b = 1 common-majorant slope used in Lemma 10.28

The source defines `ξ` as the inverse of `η(x) = (exp x - 1) / x`.
The weak interface below is exactly at Proposition 10.20(ii): it records the
explicit inverse equation, differentiability, and the source lower bound for
`η'`.  It contains no DDE solution, no weighted monotonicity, and no unit-shift
ratio.

The file proves from that interface:
* the inverse-derivative formula of Proposition 10.20(ii);
* a uniform one-sided secant bound on every unit interval (`κ = 1`);
* the FTC derivative of the phase `∫ ξ` (10.43);
* the normalized logarithmic derivative identity (10.44), with the audited
  correction `ξ(s / b)` (hence `ξ s` when `b = 1`).
-/

/-- Weak, source-faithful Proposition 10.20(ii) interface for `ξ` on `(1,∞)`.
The field `etaSlopeLower` is the displayed strict `> 1/2` estimate in the
proposition; it is not a Lemma 10.28 conclusion. -/
structure Proposition1020Xi (ξ : ℝ → ℝ) : Prop where
  continuous : Continuous ξ
  positive : ∀ s, 1 < s → 0 < ξ s
  equation : ∀ s, 1 < s → Real.exp (ξ s) - 1 = s * ξ s
  differentiableAt : ∀ s, 1 < s → DifferentiableAt ℝ ξ s
  etaSlopeLower : ∀ s, 1 < s → (1 / 2 : ℝ) < s - (s - 1) / ξ s

/-- Proposition 10.20(ii)'s inverse derivative formula, derived by
 differentiating the explicit equation `exp (ξ s) - 1 = s ξ(s)`. -/
theorem Proposition1020Xi.hasDerivAt
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {s : ℝ} (hs : 1 < s) :
    HasDerivAt ξ (1 / (s - (s - 1) / ξ s)) s := by
  have hpos : 0 < ξ s := hξ.positive s hs
  have hne : ξ s ≠ 0 := ne_of_gt hpos
  have hqpos : 0 < s - (s - 1) / ξ s :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (hξ.etaSlopeLower s hs)
  have hqne : s - (s - 1) / ξ s ≠ 0 := ne_of_gt hqpos
  have hd : HasDerivAt ξ (deriv ξ s) s := (hξ.differentiableAt s hs).hasDerivAt
  have heq :
      (fun u : ℝ => Real.exp (ξ u) - 1) =ᶠ[𝓝 s]
        (fun u : ℝ => u * ξ u) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact hξ.equation u hu
  have hleft : HasDerivAt (fun u : ℝ => Real.exp (ξ u) - 1)
      (Real.exp (ξ s) * deriv ξ s) s :=
    hd.exp.sub_const 1
  have hright : HasDerivAt (fun u : ℝ => u * ξ u)
      (ξ s + s * deriv ξ s) s := by
    have hprod := (hasDerivAt_id s).mul hd
    have hfun : id * ξ = (fun u : ℝ => u * ξ u) := by
      funext u
      simp only [Pi.mul_apply, id_eq]
    rw [hfun] at hprod
    simpa only [id_eq, one_mul] using hprod
  have hderivEq : Real.exp (ξ s) * deriv ξ s = ξ s + s * deriv ξ s := by
    exact hleft.unique (hright.congr_of_eventuallyEq heq)
  have hsourceEq := hξ.equation s hs
  have hexp : Real.exp (ξ s) = s * ξ s + 1 := by linarith
  have hmul : (deriv ξ s) * (s * ξ s - (s - 1)) = ξ s := by
    rw [hexp] at hderivEq
    linear_combination hderivEq
  have hdenEq : s * ξ s - (s - 1) = ξ s * (s - (s - 1) / ξ s) := by
    field_simp [hne]
    <;> ring
  have hdenNe : s * ξ s - (s - 1) ≠ 0 := by
    rw [hdenEq]
    exact mul_ne_zero hne hqne
  have hdform : deriv ξ s = ξ s / (s * ξ s - (s - 1)) := by
    apply (eq_div_iff hdenNe).2
    simpa only [mul_comm] using hmul
  apply hd.congr_deriv
  rw [hdform]
  field_simp [hne, hqne, hdenNe]
  <;> ring

/-- The Proposition 10.20 derivative is positive. -/
theorem Proposition1020Xi.deriv_pos
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {s : ℝ} (hs : 1 < s) :
    0 < deriv ξ s := by
  rw [(hξ.hasDerivAt hs).deriv]
  exact one_div_pos.mpr
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (hξ.etaSlopeLower s hs))

/-- The common derivative majorant `2` supplied by the strict `η' > 1/2`
bound in Proposition 10.20(ii). -/
theorem Proposition1020Xi.deriv_le_two
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {s : ℝ} (hs : 1 < s) :
    deriv ξ s ≤ 2 := by
  rw [(hξ.hasDerivAt hs).deriv]
  have hq : (1 / 2 : ℝ) < s - (s - 1) / ξ s := hξ.etaSlopeLower s hs
  have hq0 : 0 < s - (s - 1) / ξ s := by linarith
  apply (div_le_iff₀ hq0).2
  linarith

/-- One-sided common-majorant slope for `ξ` (the `κ = 1` specialization).
Unlike a unit-shift ratio for a DDE solution, this is a Proposition 10.20
calculus fact: every secant on `[2,∞)` has slope at most `2`. -/
theorem proposition1020_oneSidedCommonMajorantSlope
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {t s : ℝ}
    (ht : 2 ≤ t) (hts : t ≤ s) :
    ξ s - ξ t ≤ 2 * (s - t) := by
  rcases hts.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨c, hc, hcderiv⟩ := exists_hasDerivAt_eq_slope
      ξ (deriv ξ) hlt hξ.continuous.continuousOn
      (fun u hu => (hξ.differentiableAt u (by linarith [hu.1, ht])).hasDerivAt)
    have hcBound : deriv ξ c ≤ 2 :=
      hξ.deriv_le_two (by linarith [hc.1, ht])
    rw [hcderiv] at hcBound
    exact (div_le_iff₀ (sub_pos.mpr hlt)).1 hcBound

/-- The matching lower secant bound; together with the previous theorem this
is the controlled first-order input used by the Taylor steps in §10. -/
theorem proposition1020_secant_nonneg
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {t s : ℝ}
    (ht : 2 ≤ t) (hts : t ≤ s) :
    0 ≤ ξ s - ξ t := by
  rcases hts.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨c, hc, hcderiv⟩ := exists_hasDerivAt_eq_slope
      ξ (deriv ξ) hlt hξ.continuous.continuousOn
      (fun u hu => (hξ.differentiableAt u (by linarith [hu.1, ht])).hasDerivAt)
    have hcPos : 0 < deriv ξ c := hξ.deriv_pos (by linarith [hc.1, ht])
    rw [hcderiv] at hcPos
    rcases div_pos_iff.mp hcPos with hgood | hbad
    · exact hgood.1.le
    · exfalso
      linarith [hbad.2, sub_pos.mpr hlt]

/-- Uniform unit-interval form of the common majorant. -/
theorem proposition1020_unitIntervalError
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {t s : ℝ}
    (hs : 3 ≤ s) (ht : t ∈ Icc (s - 1) s) :
    |ξ t - ξ s| ≤ 2 := by
  have hlo : 2 ≤ t := by linarith [ht.1]
  have hupper := proposition1020_oneSidedCommonMajorantSlope hξ hlo ht.2
  have hlower := proposition1020_secant_nonneg hξ hlo ht.2
  have hdist : s - t ≤ 1 := by linarith [ht.1]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The `κ = 1` phase from (10.43). -/
noncomputable def xiPhase (ξ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..s, ξ t

/-- FTC-internalized equation (10.43), rather than a derivative field. -/
theorem xiPhase_hasDerivAt
    {ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) (s : ℝ) :
    HasDerivAt (xiPhase ξ) (ξ s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hξ.continuous.intervalIntegrable 1 s)
    hξ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    hξ.continuous.continuousAt

/-- Logarithm of the decreasing weighted envelope from Lemma 10.28. -/
noncomputable def logEnvelopeMinus
    (R ξ : ℝ → ℝ) (c : ℝ) (s : ℝ) : ℝ :=
  Real.log (R s) + xiPhase ξ s - c * s

/-- Audited normalized identity (10.44), specialized to `a = 2`, `b = 1`.
The source's printed `ξ(s/λ)` is inconsistent with (10.43), (10.45), and the
rest of the proof; at `b = 1` the corrected term is `ξ s`. -/
theorem lemma1028_logEnvelopeMinus_hasDerivAt
    {R ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {c s : ℝ}
    (hs : 0 < s) (hR : 0 < R s)
    (hDDE : HasDerivAt R (-(2 * R s + R (s - 1)) / s) s) :
    HasDerivAt (logEnvelopeMinus R ξ c)
      (-R (s - 1) / (s * R s) + ξ s - c - 2 / s) s := by
  have hlog := hDDE.log (ne_of_gt hR)
  have hphase := xiPhase_hasDerivAt hξ s
  have hlin : HasDerivAt (fun u : ℝ => c * u) c s :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul c
  have hsum := hlog.add hphase |>.sub hlin
  have hcoeff :
      (-(2 * R s + R (s - 1)) / s) / R s + ξ s - c =
        -R (s - 1) / (s * R s) + ξ s - c - 2 / s := by
    field_simp [ne_of_gt hs, ne_of_gt hR]
    <;> ring
  have hfun :
      ((fun y : ℝ => Real.log (R y)) + xiPhase ξ - fun u : ℝ => c * u) =
        logEnvelopeMinus R ξ c := by
    funext u
    rfl
  rw [hfun] at hsum
  exact hsum.congr_deriv hcoeff

/-- Equation (10.44) after multiplication by the positive `s R(s)`.  This is
exactly the slope-to-envelope bridge needed by the one-sided half of Lemma
10.28; it assumes a derivative sign, not a unit-shift ratio. -/
theorem lemma1028_commonMajorantSlope_of_deriv_nonpos
    {R ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {c s : ℝ}
    (hs : 0 < s) (hR : 0 < R s)
    (hDDE : HasDerivAt R (-(2 * R s + R (s - 1)) / s) s)
    (hslope : deriv (logEnvelopeMinus R ξ c) s ≤ 0) :
    -(R (s - 1)) + s * (ξ s - c - 2 / s) * R s ≤ 0 := by
  have hid := lemma1028_logEnvelopeMinus_hasDerivAt hξ (c := c) hs hR hDDE
  rw [hid.deriv] at hslope
  have hscale : 0 < s * R s := mul_pos hs hR
  have heq :
      -(R (s - 1)) + s * (ξ s - c - 2 / s) * R s =
        (s * R s) * (-R (s - 1) / (s * R s) + ξ s - c - 2 / s) := by
    field_simp [ne_of_gt hs, ne_of_gt hR]
    <;> ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hscale.le hslope

/-!
The remaining source step is genuinely Lemma 10.28, pp.53--58: prove the
nonpositive derivative sign globally from the pairing identity by the
first-crossing argument and the integration-by-parts estimate (10.53).
It is intentionally not postulated here.  In particular, no field or theorem
assumes `R(s-1) / R(s)` or the Lemma 10.29 unit-shift conclusion.
-/


end Section10Lemma1028
