import R2XiFirstKernel

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMSigma
open scoped Interval

theorem J_self {S t : ℝ} (hS : 3 ≤ S) : JKernel S S t = 0 := by
  have hS0 : S ≠ 0 := by linarith
  have hS1 : S - 1 ≠ 0 := by linarith
  simp only [JKernel, div_self hS1, log_one, zero_mul, zero_div, zero_add,
    div_self hS0, show S - 1 - 1 = S - 2 by ring]
  by_cases ht : t ∈ Icc (S - 2) (S - 2)
  · have he : t = S - 2 := le_antisymm ht.2 ht.1
    subst t
    rw [show S - 2 + 1 = S - 1 by ring,
      show S - 1 - (S - 2) = 1 by ring, mul_one, div_self hS1, log_one, mul_zero]
  · rw [indicator_of_notMem ht, zero_div, zero_mul]

theorem Xi1_self_integral {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) :
    IntervalIntegrable (fun t => f t * Xi1 S S t) volume 1 3 ∧
    (∫ t in (1 : ℝ)..3, f t * Xi1 S S t) = eProfile f S := by
  have he (t : ℝ) (ht : t ∈ uIcc 1 3) :
      f t * Xi1 S S t = f t * upperKernel S t := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    rw [Xi1_kernel_identity (by linarith) hS ht, J_self hS, zero_div, add_zero]
  exact ⟨(upperKernel_integrable hf ⟨hS, hS5⟩).congr
    (fun t ht => (he t (uIoc_subset_uIcc ht)).symm),
    (intervalIntegral.integral_congr he).trans (upperKernel_identity hf ⟨hS, hS5⟩)⟩

theorem Xi1_original_identity {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    IntervalIntegrable (fun t => f t * Xi1 s S t) volume 1 3 ∧
    (∫ t in (1 : ℝ)..3, f t * Xi1 s S t) =
      eProfile f S + (1 / 2) *
        ∫ u in (1 - 1 / s)..(1 - 1 / S),
          gProfile f (S * u) / (u * (1 - u)) := by
  rcases lt_or_eq_of_le hsS with hlt | rfl
  · have hg := J_endpoints hs hS hS5 hlt hr
    have hi := Xi1_integral_identity hf hs hS hS5 hlt hr
    have hj := gProfile_weighted_formula hf hg.1 hg.2.1 hg.2.2.1
      hg.2.2.2.1 hg.2.2.2.2
    refine ⟨hi.1, ?_⟩
    rw [hi.2, rationalWeight_rescale hg.1 hg.2.1 hg.2.2.1 (by linarith : 0 < S), hj.2]
    ring
  · simpa using Xi1_self_integral hf hS hS5

theorem Xi1_actual_feedback {δ s S : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hr : 2 ≤ S - S / s) :
    (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi1 s S t) ≤
      wuImprovementLimit true δ S + (1 / 2) *
        ∫ u in (1 - 1 / s)..(1 - 1 / S),
          wuImprovementLimit false δ (S * u) / (u * (1 - u)) := by
  have hf := wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
    (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  rcases lt_or_eq_of_le (show s ≤ S by linarith) with hlt | rfl
  · have hi := Xi1_integral_identity hf hs hS hS5 hlt hr
    have hg := J_endpoints hs hS hS5 hlt hr
    have hlem := original_lemma61 hd hdhi
    have hu := hlem.2.1 S ⟨hS, hS5⟩
    rw [upperKernel_identity hf ⟨hS, hS5⟩] at hu
    have hj := hlem.2.2 (1 - 1 / s) (1 - 1 / S) S
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
    rw [hi.2]
    linarith
  · rw [(Xi1_self_integral hf hS hS5).2]
    simpa using (actual_continuous_extension hd hdhi).2.2 s ⟨hS, hS5⟩

theorem proposition3_actual {δ s S : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hr : 2 ≤ S - S / s) :
    firstFunctionalGainPsiOne s S -
        2 * δ / (1 - 2 * δ) * omega3XIntegralEnvelope s S +
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi1 s S t) ≤
        wuImprovementLimit true δ s := by
  have hsource := wuImprovementLimit_firstFunctionalGain_source hd hdhi hs hs3 hS hS5 hr
  have hkernel := Xi1_actual_feedback hd hdhi hs hs3 hS hS5 hr
  linarith

theorem proposition3_delta_psi {δ s S : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hr : 2 ≤ S - S / s) :
    firstFunctionalGainPsi δ s S +
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi1 s S t) ≤
        wuImprovementLimit true δ s := by
  rw [firstFunctionalGainPsi_eq_source_sub_penalty (by linarith : δ < 1 / 2)
    hs hs3 hS hS5]
  exact proposition3_actual hd hdhi hs hs3 hS hS5 hr

theorem proposition3_five_original_rows {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (i : Fin 5) :
    firstFunctionalGainPsi δ (ActualNineFeedback.firstNode i) (ActualNineFeedback.firstS i) +
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t *
        Xi1 (ActualNineFeedback.firstNode i) (ActualNineFeedback.firstS i) t) ≤
      wuImprovementLimit true δ (ActualNineFeedback.firstNode i) := by
  rcases WuPaper.RMapMMatrix.original_five_rows_qualified i with ⟨hs, hs3, hS, hS5, hr⟩
  exact proposition3_delta_psi hd hdhi hs hs3 hS hS5 hr

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
