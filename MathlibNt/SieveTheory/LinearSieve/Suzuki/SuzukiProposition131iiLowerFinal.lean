import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1022LowerBarrier
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiQhatLocal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerInternal

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- An exported spelling of the (private) constant in Proposition 10.23. -/
noncomputable def proposition131iiPhaseConstant : ℝ :=
  Section10CanonicalXi.xi (Real.exp 2) +
    Real.log (Section10CanonicalXi.xi (Real.exp 2) + 3)

lemma proposition1023_coarse_phase_exported :
    ∀ᶠ s : ℝ in atTop,
      (∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) ≤
        s * Real.log s + s * Real.log (Real.log (3 * s)) +
          proposition131iiPhaseConstant * s := by
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with s hs
  have hs1 : 1 ≤ s := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).le.trans hs
  have hxiInt : IntervalIntegrable Section10CanonicalXi.xi volume (1 : ℝ) s :=
    Section10CanonicalXi.xi_continuous.intervalIntegrable 1 s
  let M := Real.log s + Real.log (Real.log (3 * s)) + proposition131iiPhaseConstant
  have hMInt : IntervalIntegrable (fun _ : ℝ => M) volume 1 s :=
    continuous_const.intervalIntegrable 1 s
  have hmono : (∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) ≤
      ∫ _t in (1 : ℝ)..s, M := by
    apply intervalIntegral.integral_mono_on hs1 hxiInt hMInt
    intro t ht
    have h := Section10CanonicalXi.coarse_phase_uniform_on_Icc hs ht
    change Section10CanonicalXi.xi t ≤
      Real.log s + Real.log (Real.log (3 * s)) + proposition131iiPhaseConstant at h
    exact h
  rw [intervalIntegral.integral_const] at hmono
  change (∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) ≤ (s - 1) * M at hmono
  have hspos : 0 < s := (Real.exp_pos 2).trans_le hs
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hloglog : 0 ≤ Real.log (Real.log (3 * s)) := by
    apply Real.log_nonneg
    have hlogs2 : 2 ≤ Real.log s := by
      rw [← Real.exp_log hspos] at hs
      exact Real.exp_le_exp.mp hs
    have hm := Real.strictMonoOn_log.monotoneOn hspos
      (mul_pos (by norm_num) hspos) (by nlinarith : s ≤ 3 * s)
    linarith
  have hA0 : 0 ≤ proposition131iiPhaseConstant := by
    unfold proposition131iiPhaseConstant
    have hx := Section10CanonicalXi.xi_pos
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2))
    have hl : 0 ≤ Real.log (Section10CanonicalXi.xi (Real.exp 2) + 3) :=
      Real.log_nonneg (by linarith)
    linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  calc
    (∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) ≤ (s - 1) * M := hmono
    _ ≤ s * M := by nlinarith
    _ = s * Real.log s + s * Real.log (Real.log (3 * s)) +
        proposition131iiPhaseConstant * s := by dsimp [M]; ring

/-- Proposition 13.1(ii), lower half, uniformly for the two signs.  All analytic
inputs are extracted from the Section-13 source contract. -/
theorem proposition131iiUniformQuantitativeLower_of_source
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Proposition131iiUniformQuantitativeLower H := by
  have hlocal := section13Qhat_lemma1022_local_premise hH
  have hlocal' : ∀ᶠ s : ℝ in atTop,
      (s + 1) * section13Qhat H s ≥
        1 * ∫ t in s - 1..s, section13Qhat H t := by
    simpa only [one_mul] using hlocal
  obtain ⟨c, hc, hbarrier⟩ :=
    Section10Lemma1022.lemma10_22_lower_barrier_one
      (E := (1 : ℝ)) (s₀ := (1 : ℝ))
      (f := section13Qhat H) (by norm_num) (by norm_num)
      (section13Qhat_continuousOn hH.toSection13HatContract |>.mono (by
        intro s hs
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs))
      (fun s hs => section13Qhat_pos hH.toSection13HatContract
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs))
      (by simpa only [one_mul] using hlocal')
  let A : ℝ := proposition131iiPhaseConstant
  have hphase : ∀ᶠ s : ℝ in atTop,
      (∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) ≤
        s * Real.log s + s * Real.log (Real.log (3 * s)) + A * s := by
    simpa [A] using proposition1023_coarse_phase_exported
  obtain ⟨η, hη, hη1, hcomparison⟩ :=
    BridgeAssembly.section13_global_uniform_eta hH
  let a : ℝ := (1 - η) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let C : ℝ := max 0 A + c * (1 + Real.exp 1) + |Real.log a|
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have htail : ∀ᶠ s : ℝ in atTop,
      ∀ sign : ErrorSign, proposition131iiLowerProfile C s ≤ H.T sign s := by
    filter_upwards [hbarrier, hphase, eventually_ge_atTop (3 : ℝ)] with s hbar hph hs
    have hspos : 0 < s := by linarith
    have harg : 0 < s + Real.exp 1 := add_pos hspos (Real.exp_pos 1)
    have hlogarg : Real.log (s + Real.exp 1) ≤ s + Real.exp 1 := by
      have h := Real.log_le_sub_one_of_pos harg
      linarith
    have hc0 : 0 ≤ c := le_trans (by norm_num) hc
    have hclog : c * Real.log (s + Real.exp 1) ≤ c * (1 + Real.exp 1) * s := by
      have hmul := mul_le_mul_of_nonneg_left hlogarg hc0
      have hce : c * Real.exp 1 ≤ c * Real.exp 1 * s := by
        nlinarith [mul_nonneg hc0 (Real.exp_pos 1).le]
      nlinarith
    have hA : A ≤ max 0 A := le_max_right 0 A
    have hmaxA0 : 0 ≤ max 0 A := le_max_left 0 A
    have habs0 : 0 ≤ |Real.log a| := abs_nonneg _
    have hlogA : -Real.log a ≤ |Real.log a| := neg_le_abs _
    have hlogScaled : -Real.log a ≤ |Real.log a| * s := by
      calc
        -Real.log a ≤ |Real.log a| := hlogA
        _ ≤ |Real.log a| * s := by nlinarith
    have hexponent :
        -s * Real.log s - s * Real.log (Real.log (3 * s)) - C * s ≤
          Real.log a -
            ((∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) +
              c * Real.log (s + Real.exp 1)) := by
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right hA hspos.le]
    have hbar' :
        Real.exp (-(∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) -
          c * Real.log (s + Real.exp 1)) < section13Qhat H s := by
      simpa using hbar
    have hprofileQ : proposition131iiLowerProfile C s <
        a * section13Qhat H s := by
      have hexp := Real.exp_le_exp.mpr hexponent
      have halog : Real.exp (Real.log a -
            ((∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) +
              c * Real.log (s + Real.exp 1))) =
          a * Real.exp (-(∫ t in (1 : ℝ)..s, Section10CanonicalXi.xi t) -
              c * Real.log (s + Real.exp 1)) := by
        rw [Real.exp_sub, Real.exp_log ha]
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
      unfold proposition131iiLowerProfile
      rw [halog] at hexp
      exact hexp.trans_lt (mul_lt_mul_of_pos_left hbar' ha)
    intro sign
    have hcmp := section13_comparison_of_P_abs_le hη.le hη1 (hcomparison s hs)
    cases sign with
    | plus =>
        exact hprofileQ.le.trans hcmp.1
    | minus =>
        exact hprofileQ.le.trans hcmp.2.2.1
  rcases eventually_atTop.1 htail with ⟨M₀, hM₀⟩
  let M : ℝ := max 3 M₀
  refine ⟨C, M, hC, le_max_left _ _, ?_⟩
  intro sign s hs
  exact hM₀ s (le_trans (le_max_right 3 M₀) hs) sign


end MathlibNt.SieveTheory
