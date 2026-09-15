import MathlibNt.Wu2008DoubleSieve.FirstFeedbackLower
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackAssemblyIntegral

/-!
# Wu04 Proposition 3 for the actual fixed-delta gains

Author TeX lines 1243--1259 and 2614--2619. The three proved parts of
Lemma 6.1 convert the accepted first functional inequality into the
literal `Xi1` feedback bound. The coefficient retains the full
`I(s,t)/(1-2*delta)` loss. This is not the final 0.899 counting theorem.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

/-- Lemma 6.1 pays the exact source feedback integral, without an analytic premise. -/
theorem wuImprovementLimit_firstFeedback_integral_le {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x * firstFeedbackXi x s t) ≤
      wuImprovementLimit true δ t +
        (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
          wuImprovementLimit false δ (t * u) / (u * (1 - u))) := by
  rw [wuImprovementLimit_firstFeedback_assembly_integral hδ hδhi hs hs3 ht ht5 hratio]
  have hupper := wuImprovementLimit_firstFeedback_62_split hδ hδhi ht ht5
  have hlower := wuImprovementLimit_firstFeedback_63_parameters
    hδ hδhi hs hs3 ht ht5 hratio
  linarith

/-- Wu04 Proposition 3, with actual fixed-delta H/h and the accepted Psi coefficient. -/
theorem wuImprovementLimit_firstFeedback {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    firstFunctionalGainPsi δ s t +
      (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x * firstFeedbackXi x s t) ≤
      wuImprovementLimit true δ s := by
  have hfirst := wuImprovementLimit_firstFunctionalGain hδ hδhi hs hs3 ht ht5 hratio
  have hfeedback := wuImprovementLimit_firstFeedback_integral_le
    hδ hδhi hs hs3 ht ht5 hratio
  linarith

/-- The source Psi1 form displays, rather than discards, the fixed-delta penalty. -/
theorem wuImprovementLimit_firstFeedback_source {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    firstFunctionalGainPsiOne s t -
        (2 * δ / (1 - 2 * δ)) * omega3XIntegralEnvelope s t +
      (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x * firstFeedbackXi x s t) ≤
      wuImprovementLimit true δ s := by
  rw [← firstFunctionalGainPsi_eq_source_sub_penalty (by linarith) hs hs3 ht ht5]
  exact wuImprovementLimit_firstFeedback hδ hδhi hs hs3 ht ht5 hratio

/-- The valid `s = t = 3` degeneration is included without a strict-interval lemma. -/
theorem wuImprovementLimit_firstFeedback_three {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x * firstFeedbackXi x 3 3) ≤
      wuImprovementLimit true δ 3 := by
  have h := wuImprovementLimit_firstFeedback hδ hδhi
    (s := 3) (t := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simpa only [firstFunctionalGainPsi_self, zero_add] using h

end Wu2008DoubleSieve
