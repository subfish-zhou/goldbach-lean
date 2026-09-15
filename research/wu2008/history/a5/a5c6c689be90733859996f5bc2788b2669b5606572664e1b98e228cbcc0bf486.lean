import R2MatrixXi2Terms

noncomputable section
namespace WuPaper.R2Matrix
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval BigOperators

theorem xi2_power_endpoints (i : Fin 4) :
    xi2Product (coupledRow i) ≤ (alpha2 (coupledRow i) + 1)^5 ∧
    ((coupledRow i).kappa1 - 1) * ((coupledRow i).kappa2 - 1) ≤
      (alpha1 (coupledRow i) + 1)^2 := by
  fin_cases i <;>
    norm_num [xi2Product, alpha1, alpha2, coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem xi2_product_log_ratio (i : Fin 4) {t : ℝ}
    (ht : t ∈ Icc (xi2Left (coupledRow i) 5) (xi2Right (coupledRow i) 5)) :
    xi2Denominator (coupledRow i) t 5 ≤ xi2Numerator (coupledRow i) t 5 := by
  let p := coupledRow i
  have hk1 : 0 ≤ p.kappa1 := by
    have h := (coupledRow_geometry i).2.1
    change 3 ≤ p.kappa1 at h
    linarith only [h]
  have hk3 : 0 ≤ p.kappa3 := by
    have h := (coupled_geometry_bounds (coupledRow_geometry i)).2.2.2.2.1
    change 2 ≤ p.kappa3 at h
    linarith only [h]
  have hlo : alpha7 p ≤ t := ht.1
  have hhi : t ≤ alpha5 p := ht.2
  have hp := xi2_product_factors_positive i
  change 0 < p.kappa1 * p.S - p.S - p.kappa1 * alpha5 p ∧
    0 < p.kappa3 * p.S - p.S - p.kappa3 * alpha5 p at hp
  have h1 := sub_le_sub_left (mul_le_mul_of_nonneg_left hlo hk1) (p.kappa1 * p.S - p.S)
  have h2 := sub_le_sub_left (mul_le_mul_of_nonneg_left hlo hk3) (p.kappa3 * p.S - p.S)
  have ht1 := hp.1.trans_le
    (sub_le_sub_left (mul_le_mul_of_nonneg_left hhi hk1) (p.kappa1 * p.S - p.S))
  have ht2 := hp.2.trans_le
    (sub_le_sub_left (mul_le_mul_of_nonneg_left hhi hk3) (p.kappa3 * p.S - p.S))
  have he :
      (p.kappa1 * p.S - p.S - p.kappa1 * alpha7 p) *
      (p.kappa3 * p.S - p.S - p.kappa3 * alpha7 p) = p.S^2 := by
    dsimp [p]
    fin_cases i <;>
      norm_num [alpha7, coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]
  exact (mul_le_mul h1 h2 ht2.le (ht1.le.trans h1)).trans_eq he

theorem xi2_ratio_at_least_one (i : Fin 4) (j : Fin 9) {t : ℝ}
    (ht : t ∈ Icc (xi2Left (coupledRow i) j) (xi2Right (coupledRow i) j)) :
    xi2Denominator (coupledRow i) t j ≤ xi2Numerator (coupledRow i) t j := by
  fin_cases j
  · change xi2Product (coupledRow i) ≤ (t + 1)^5
    apply (xi2_power_endpoints i).1.trans
    have hl : alpha2 (coupledRow i) ≤ t := ht.1
    have ha : 1 ≤ alpha2 (coupledRow i) := (xi2_support_geometry i 0).1
    gcongr
  · fin_cases i <;>
      norm_num [xi2Denominator, xi2Numerator, xi2Left, xi2Right, alpha9, alpha1,
        coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  · fin_cases i <;>
      norm_num [xi2Denominator, xi2Numerator, xi2Left, xi2Right, alpha5, alpha2,
        coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  · fin_cases i <;>
      norm_num [xi2Denominator, xi2Numerator, xi2Left, xi2Right, alpha3, alpha2,
        coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  · change ((coupledRow i).kappa1 - 1) * ((coupledRow i).kappa2 - 1) ≤ (t + 1)^2
    apply (xi2_power_endpoints i).2.trans
    have hl : alpha1 (coupledRow i) ≤ t := ht.1
    have ha : 1 ≤ alpha1 (coupledRow i) := (xi2_support_geometry i 4).1
    gcongr
  · exact xi2_product_log_ratio i ht
  · fin_cases i <;>
      norm_num [xi2Denominator, xi2Numerator, xi2Left, xi2Right, alpha5, alpha8,
        coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  · fin_cases i <;>
      norm_num [xi2Denominator, xi2Numerator, xi2Left, xi2Right, alpha6, alpha8,
        coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  · fin_cases i <;>
      norm_num [xi2Denominator, xi2Numerator, xi2Left, xi2Right, alpha8, alpha2,
        coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
      linarith only [ht.1, ht.2]

theorem xi2_nonnegative (i : Fin 4) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    0 ≤ xi2 t (coupledRow i) := by
  unfold xi2
  apply add_nonneg
  · exact mul_nonneg (div_nonneg (sigma0_nonneg ht) (by linarith [ht.1]))
      (log_nonneg ((one_le_div (xi2_product_bounds i).1).mpr (xi2_product_bounds i).2))
  · apply Finset.sum_nonneg
    intro j _
    by_cases hm : t ∈ Icc (xi2Left (coupledRow i) j) (xi2Right (coupledRow i) j)
    · rw [indicator_of_mem hm, one_mul]
      exact div_nonneg (log_nonneg ((one_le_div (xi2_denominator_positive i j hm)).mpr
        (xi2_ratio_at_least_one i j hm))) (xi2_scale_positive i j ht).le
    · rw [indicator_of_notMem hm, zero_mul]

theorem xi2_weighted_integrable (i : Fin 4) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun t => f t * xi2 t (coupledRow i)) volume 1 3 := by
  have hi1 := (WuPaper.RMapMSigma.sigma_weight_integrable hf).mul_const
    (log (1024 / xi2Product (coupledRow i)) / 5)
  have hi2 : IntervalIntegrable (fun t => ∑ j : Fin 9,
      f t * (Icc (xi2Left (coupledRow i) j) (xi2Right (coupledRow i) j)).indicator
        (fun _ => (1 : ℝ)) t * xi2Weight (coupledRow i) j t) volume 1 3 := by
    have hi (j : Fin 9) := supported_weight_integrable hf (xi2_support_geometry i j).1
      (xi2_support_geometry i j).2.1 (xi2_support_geometry i j).2.2
      (xi2_weight_continuous i j)
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun j _ => hi j)
  convert hi1.add hi2 using 1
  ext t
  dsimp [xi2]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem xi2_integrable (i : Fin 4) :
    IntervalIntegrable (fun t => xi2 t (coupledRow i)) volume 1 3 := by
  simpa only [one_mul] using xi2_weighted_integrable i
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 3)

theorem second_original_coefficients_nonnegative (i : Fin 4) (k : Fin 9) :
    0 ≤ ∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
      xi2 t (coupledRow i) := by
  have hb := source_cell_bounds k
  apply intervalIntegral.integral_nonneg hb.2.1
  intro t ht
  exact xi2_nonnegative i ⟨hb.1.trans ht.1, ht.2.trans hb.2.2⟩

theorem second_original_H_discretization (i : Fin 4) {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    (∑ k : Fin 9,
      (∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
        xi2 t (coupledRow i)) * actualNine δ k) ≤
      ∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * xi2 t (coupledRow i) := by
  exact original_monotone_discretization hd hh (xi2_integrable i)
    (xi2_weighted_integrable i (wuImprovementLimit_intervalIntegrable true hd
      (by linarith : δ < 1 / 2) (by norm_num) (by norm_num) (by norm_num)))
    (fun _ ht => xi2_nonnegative i ht)

end WuPaper.R2Matrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
