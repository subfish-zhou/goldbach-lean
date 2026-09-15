import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146Quantitative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146iErrorEnvelopeTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

private theorem perturbation_div_antitoneOn_lowStrip
    {D d : ℝ} (hd : 0 ≤ d) (hD : 1 < D)
    (hlarge : (1 + 3 * d) * (4 : ℝ) ^ d ≤ (1 / 3 : ℝ) * Real.log D) :
    AntitoneOn (fun t : ℝ => perturbation D d 0 t / t) (Icc 1 3) := by
  have hlog : 0 < Real.log D := Real.log_pos hD
  apply antitoneOn_of_deriv_nonpos (convex_Icc (1 : ℝ) 3)
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    exact ((hasDerivAt_perturbation (D := D) (d := d) (ε := 0) hlog
      (by simpa using ht0)).div (hasDerivAt_id t) ht0.ne').continuousAt.continuousWithinAt
  · intro t ht
    have htI : t ∈ Icc (1 : ℝ) 3 := interior_subset ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htI.1
    exact ((hasDerivAt_perturbation (D := D) (d := d) (ε := 0) hlog
      (by simpa using ht0)).div (hasDerivAt_id t) ht0.ne').differentiableAt.differentiableWithinAt
  · intro t ht
    have htI : t ∈ Icc (1 : ℝ) 3 := interior_subset ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htI.1
    have hslope := perturbationSlope_le (D := D) (d := d) (ε := 0)
      (t := t) (σ := 3) hlog hd htI.1 htI.2 (by norm_num) (by norm_num)
    have hslopeThird : perturbationSlope D d 0 t ≤ (1 / 3 : ℝ) := by
      apply hslope.trans
      rw [div_le_iff₀ hlog]
      simpa only [show (3 + 1 : ℝ) = 4 by norm_num] using hlarge
    have hthirdInv : (1 / 3 : ℝ) ≤ 1 / t := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) ht0]
      nlinarith [htI.2]
    have hP0 : 0 ≤ perturbation D d 0 t := by
      apply Real.rpow_nonneg
      have hz : 0 ≤ t ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg ht0.le _) hlog.le
      simpa [perturbation] using (show 0 ≤ 1 + t ^ d / Real.log D by linarith)
    have hderiv := ((hasDerivAt_perturbation (D := D) (d := d) (ε := 0) hlog
      (by simpa using ht0)).div (hasDerivAt_id t) ht0.ne').deriv
    have hfun : (fun z => perturbation D d 0 z / z) = perturbation D d 0 / id := by
      funext z
      rfl
    have hderiv' : deriv (fun z => perturbation D d 0 z / z) t =
        (perturbation D d 0 t * perturbationSlope D d 0 t * t -
          perturbation D d 0 t * 1) / t ^ 2 := by
      rw [hfun]
      simpa [perturbationSlope] using hderiv
    rw [hderiv']
    change (perturbation D d 0 t * perturbationSlope D d 0 t * t -
      perturbation D d 0 t * 1) / t ^ 2 ≤ 0
    have hs : perturbationSlope D d 0 t ≤ 1 / t := hslopeThird.trans hthirdInv
    have hnum : perturbation D d 0 t * perturbationSlope D d 0 t * t -
        perturbation D d 0 t * 1 ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hs hP0
      have hmul := mul_le_mul_of_nonneg_right this ht0.le
      calc
        perturbation D d 0 t * perturbationSlope D d 0 t * t -
            perturbation D d 0 t * 1 ≤
          perturbation D d 0 t * (1 / t) * t -
            perturbation D d 0 t * 1 := sub_le_sub_right hmul _
        _ = 0 := by field_simp [ht0.ne']; ring
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg t)

/-- On the odd predecessor's initial strip, the exact Section-13 value
`weightedHat H plus = 1` turns the envelope into `perturbation/t`; for a
large enough recursive argument this quotient is antitone on `[1,3]`. -/
theorem errorEnvelope_antitoneOn_plus_lowStrip
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {N : ℕ} {D d : ℝ} (hsign : ErrorSign.ofDepth N = .plus)
    (hd : 0 ≤ d) (hD : 1 < D)
    (hlarge : (1 + 3 * d) * (4 : ℝ) ^ d ≤ (1 / 3 : ℝ) * Real.log D) :
    AntitoneOn (errorEnvelope H N D d) (Icc 1 3) := by
  have hpert := perturbation_div_antitoneOn_lowStrip hd hD hlarge
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have hWx : weightedHat H (ErrorSign.ofDepth N) x = 1 := by
    rw [hsign]
    have hi := hH.initial_plus x hx0 (by norm_num at hx ⊢; exact hx.2)
    norm_num at hi ⊢
    exact hi
  have hWy : weightedHat H (ErrorSign.ofDepth N) y = 1 := by
    rw [hsign]
    have hi := hH.initial_plus y hy0 (by norm_num at hy ⊢; exact hy.2)
    norm_num at hi ⊢
    exact hi
  rw [errorEnvelope_eq_lambda_div_internal H hy0,
    errorEnvelope_eq_lambda_div_internal H hx0,
    lambda_eq_perturb_mul_weightedHat,
    lambda_eq_perturb_mul_weightedHat, hWy, hWx, mul_one, mul_one]
  exact hpert hx hy hxy

/-- Full coordinate transport.  The minus predecessor is already in the
Claim-14.6(i) interval.  For the plus predecessor, the proof uses the exact
initial formula below `3`, Claim 14.6(i) above `3`, and composes the two bounds
when the coordinate pair crosses `3`. -/
theorem errorEnvelope_coordinate_transport_full
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {N : ℕ} {D d σ x y : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D)
    (hlarge : (1 + 3 * d) * (4 : ℝ) ^ d ≤ (1 / 3 : ℝ) * Real.log D)
    (hi : Claim14_6_MonotoneLambdaPremise H D d σ)
    (hxdom : x ∈ KappaOneModel.parityDomain 2 N)
    (hxy : x ≤ y) (hyσ : y ≤ σ) :
    errorEnvelope H N D d y ≤ errorEnvelope H N D d x := by
  rcases Nat.even_or_odd N with hNeven | hNodd
  · have hsign : ErrorSign.ofDepth N = .minus := ErrorSign.ofDepth_of_even hNeven
    have hnmod : N % 2 = 0 := Nat.even_iff.mp hNeven
    have hx2 : 2 ≤ x := by
      simpa [KappaOneModel.parityDomain, hnmod] using hxdom
    have hanti := errorEnvelope_antitoneOn_of_claim14_6_internal N hH hD hi
    apply hanti
    · constructor
      · simpa [hH.betaHat_eq, hsign, ErrorSign.epsilon] using hx2
      · exact hxy.trans hyσ
    · constructor
      · exact (by simpa [hH.betaHat_eq, hsign, ErrorSign.epsilon] using hx2.trans hxy)
      · exact hyσ
    · exact hxy
  · have hsign : ErrorSign.ofDepth N = .plus := ErrorSign.ofDepth_of_odd hNodd
    have hnmod : N % 2 = 1 := Nat.odd_iff.mp hNodd
    have hx1 : 1 < x := by
      simp [KappaOneModel.parityDomain, hnmod] at hxdom
      norm_num at hxdom ⊢
      exact hxdom
    have hlow := errorEnvelope_antitoneOn_plus_lowStrip hH hsign hd hD hlarge
    by_cases hy3 : y ≤ 3
    · exact hlow ⟨hx1.le, hxy.trans hy3⟩ ⟨hx1.le.trans hxy, hy3⟩ hxy
    · have h3y : 3 < y := lt_of_not_ge hy3
      have hanti := errorEnvelope_antitoneOn_of_claim14_6_internal N hH hD hi
      by_cases h3x : 3 ≤ x
      · apply hanti
        · constructor
          · rw [hH.betaHat_eq, hsign]
            norm_num [ErrorSign.epsilon]
            exact h3x
          · exact hxy.trans hyσ
        · constructor
          · rw [hH.betaHat_eq, hsign]
            norm_num [ErrorSign.epsilon]
            exact h3y.le
          · exact hyσ
        · exact hxy
      · have hx3 : x < 3 := lt_of_not_ge h3x
        have hlowPart : errorEnvelope H N D d 3 ≤ errorEnvelope H N D d x :=
          hlow ⟨hx1.le, hx3.le⟩ ⟨by norm_num, le_rfl⟩ hx3.le
        have hhighPart : errorEnvelope H N D d y ≤ errorEnvelope H N D d 3 := by
          apply hanti
          · constructor
            · rw [hH.betaHat_eq, hsign]
              norm_num [ErrorSign.epsilon]
            · exact h3y.le.trans hyσ
          · constructor
            · rw [hH.betaHat_eq, hsign]
              norm_num [ErrorSign.epsilon]
              exact h3y.le
            · exact hyσ
          · exact h3y.le
        exact hhighPart.trans hlowPart


end MathlibNt.SieveTheory
