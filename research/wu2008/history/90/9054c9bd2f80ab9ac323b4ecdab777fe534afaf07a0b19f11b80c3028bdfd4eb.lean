import R2MatrixCells

noncomputable section
namespace WuPaper.R2Matrix
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval BigOperators

theorem first_support_geometry (i : Fin 5) :
    1 ≤ Wu04Source.alpha3 (firstNode i) (firstS i) ∧
    Wu04Source.alpha3 (firstNode i) (firstS i) ≤ Wu04Source.alpha2 (firstS i) ∧
    1 ≤ Wu04Source.alpha2 (firstS i) ∧ Wu04Source.alpha2 (firstS i) ≤ 3 := by
  fin_cases i <;> norm_num [Wu04Source.alpha3, Wu04Source.alpha2, firstNode, firstS]

theorem xi1_nonnegative (i : Fin 5) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    0 ≤ Wu04Source.xi1 t (firstNode i) (firstS i) := by
  let s := firstNode i
  let S := firstS i
  have hg := first_geometry i
  have hs : 2 ≤ s := hg.1
  have hs3 : s ≤ 3 := hg.2.1
  have hS : 3 ≤ S := hg.2.2.1
  have hS5 : S ≤ 5 := hg.2.2.2.1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have hD : 0 < (s - 1) * (S - 1) := mul_pos (by linarith) (by linarith)
  have hD16 : (s - 1) * (S - 1) ≤ 16 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 3 - s) (by linarith : 0 ≤ S - 1)]
  change 0 ≤ Wu04Source.xi1 t s S
  unfold Wu04Source.xi1
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg
        (div_nonneg (sigma0_nonneg ht) (by linarith [ht.1]))
        (log_nonneg ((one_le_div hD).mpr hD16))
    · by_cases hm : t ∈ Icc (Wu04Source.alpha2 S) 3
      · rw [indicator_of_mem hm]
        have htl : S - 2 ≤ t := hm.1
        apply mul_nonneg (by positivity)
        apply log_nonneg
        apply (one_le_div hD).mpr
        nlinarith [sq_nonneg (t + 1 - (S - 1)),
          mul_nonneg (by linarith : 0 ≤ t + 1 - (S - 1))
            (by linarith : 0 ≤ t + 1 + (S - 1)),
          mul_nonneg (by linarith : 0 ≤ S - s) (by linarith : 0 ≤ S - 1)]
      · rw [indicator_of_notMem hm]
        simp
  · by_cases hm : t ∈ Icc (Wu04Source.alpha3 s S) (Wu04Source.alpha2 S)
    · rw [indicator_of_mem hm]
      have hlo : S - S / s - 1 ≤ t := hm.1
      have hhi : t ≤ S - 2 := hm.2
      have hd : 0 < (s - 1) * (S - 1 - t) := mul_pos (by linarith) (by linarith)
      have he : s * (S - S / s - 1) = s * S - S - s := by
        field_simp
      have hm' := mul_le_mul_of_nonneg_left hlo hs0.le
      rw [he] at hm'
      exact mul_nonneg (by positivity)
        (log_nonneg ((one_le_div hd).mpr (by nlinarith)))
    · rw [indicator_of_notMem hm]
      simp

theorem xi1_weighted_integrable (i : Fin 5) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun t => f t * Wu04Source.xi1 t (firstNode i) (firstS i))
      volume 1 3 := by
  let s := firstNode i
  let S := firstS i
  have hg := first_geometry i
  have hs : 2 ≤ s := hg.1
  have hS : 3 ≤ S := hg.2.2.1
  have hb := first_support_geometry i
  have hD : 0 < (s - 1) * (S - 1) := mul_pos (by linarith) (by linarith)
  have h2 : ContinuousOn (fun t : ℝ => log ((t + 1)^2 / ((s - 1) * (S - 1))) / (2 * t))
      (Icc (Wu04Source.alpha2 S) 3) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith [hb.2.2.1]) ht.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have h3 : ContinuousOn (fun t : ℝ => log ((t + 1) / ((s - 1) * (S - 1 - t))) / (2 * t))
      (Icc (Wu04Source.alpha3 s S) (Wu04Source.alpha2 S)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith [hb.1]) ht.1
    have hd : 0 < S - 1 - t := by
      have hh : t ≤ S - 2 := ht.2
      linarith
    have hs0 : 0 < s - 1 := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hi2 := supported_weight_integrable hf hb.2.2.1 hb.2.2.2 le_rfl h2
  have hi3 := supported_weight_integrable hf hb.1 hb.2.1 hb.2.2.2 h3
  have hi1 := (WuPaper.RMapMSigma.sigma_weight_integrable hf).mul_const
    (log (16 / ((s - 1) * (S - 1))) / 2)
  convert (hi1.add hi2).add hi3 using 1
  ext t
  dsimp [Wu04Source.xi1, Wu04Source.paperSigma0_eq]
  ring

theorem xi1_integrable (i : Fin 5) :
    IntervalIntegrable (fun t => Wu04Source.xi1 t (firstNode i) (firstS i)) volume 1 3 := by
  simpa only [one_mul] using xi1_weighted_integrable i
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 3)

theorem first_original_coefficients_nonnegative (i : Fin 5) (k : Fin 9) :
    0 ≤ ∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
      Wu04Source.xi1 t (firstNode i) (firstS i) := by
  have hb := source_cell_bounds k
  apply intervalIntegral.integral_nonneg hb.2.1
  intro t ht
  exact xi1_nonnegative i ⟨hb.1.trans ht.1, ht.2.trans hb.2.2⟩

theorem first_original_H_discretization (i : Fin 5) {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    (∑ k : Fin 9,
      (∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
        Wu04Source.xi1 t (firstNode i) (firstS i)) * actualNine δ k) ≤
      ∫ t in (1 : ℝ)..3,
        wuImprovementLimit true δ t * Wu04Source.xi1 t (firstNode i) (firstS i) := by
  exact original_monotone_discretization hd hh (xi1_integrable i)
    (xi1_weighted_integrable i (wuImprovementLimit_intervalIntegrable true hd
      (by linarith : δ < 1 / 2) (by norm_num) (by norm_num) (by norm_num)))
    (fun _ ht => xi1_nonnegative i ht)

end WuPaper.R2Matrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
