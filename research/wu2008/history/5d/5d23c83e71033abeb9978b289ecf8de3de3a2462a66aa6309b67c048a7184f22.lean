import R2MatrixXi1

noncomputable section
namespace WuPaper.R2Matrix
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval BigOperators

def xi2Product (p : SecondFunctionalParameters) : ℝ :=
  (p.s - 1) * (p.S - 1) * (p.kappa1 - 1) * (p.kappa2 - 1) * (p.kappa3 - 1)

def xi2Left (p : SecondFunctionalParameters) : Fin 9 → ℝ :=
  ![alpha2 p, alpha9 p, alpha5 p, alpha3 p, alpha1 p,
    alpha7 p, alpha5 p, alpha6 p, alpha8 p]

def xi2Right (p : SecondFunctionalParameters) : Fin 9 → ℝ :=
  ![3, alpha1 p, alpha2 p, alpha2 p, alpha2 p,
    alpha5 p, alpha8 p, alpha8 p, alpha2 p]

def xi2Numerator (p : SecondFunctionalParameters) (t : ℝ) : Fin 9 → ℝ :=
  ![(t + 1)^5, t + 1, t + 1, t + 1, (t + 1)^2,
    p.S^2, p.S * (p.S - 1 - t), p.S, p.S - 1 - t]

def xi2Denominator (p : SecondFunctionalParameters) (t : ℝ) : Fin 9 → ℝ :=
  ![xi2Product p, (p.kappa2 - 1) * (p.kappa1 - 1 - t),
    (p.kappa3 - 1) * (p.S - 1 - t), (p.s - 1) * (p.S - 1 - t),
    (p.kappa1 - 1) * (p.kappa2 - 1),
    (p.kappa1 * p.S - p.S - p.kappa1 * t) * (p.kappa3 * p.S - p.S - p.kappa3 * t),
    p.kappa1 * p.S - p.S - p.kappa1 * t,
    p.kappa2 * p.S - p.S - p.kappa2 * t, 1]

def xi2Scale (p : SecondFunctionalParameters) (t : ℝ) (j : Fin 9) : ℝ :=
  if j.val < 5 then 5 * t else 5 * t * (1 - t / p.S)

def xi2Weight (p : SecondFunctionalParameters) (j : Fin 9) (t : ℝ) : ℝ :=
  log (xi2Numerator p t j / xi2Denominator p t j) / xi2Scale p t j

def xi2 (t : ℝ) (p : SecondFunctionalParameters) : ℝ :=
  sigma0 t / (5 * t) * log (1024 / xi2Product p) +
    ∑ j : Fin 9, (Icc (xi2Left p j) (xi2Right p j)).indicator
      (fun _ => (1 : ℝ)) t * xi2Weight p j t

theorem xi2_literal (t : ℝ) (p : SecondFunctionalParameters) :
    xi2 t p =
    sigma0 t / (5 * t) * log (1024 / xi2Product p) +
    (Icc (alpha2 p) 3).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
      log ((t + 1)^5 / xi2Product p) +
    (Icc (alpha9 p) (alpha1 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
      log ((t + 1) / ((p.kappa2 - 1) * (p.kappa1 - 1 - t))) +
    (Icc (alpha5 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
      log ((t + 1) / ((p.kappa3 - 1) * (p.S - 1 - t))) +
    (Icc (alpha3 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
      log ((t + 1) / ((p.s - 1) * (p.S - 1 - t))) +
    (Icc (alpha1 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
      log ((t + 1)^2 / ((p.kappa1 - 1) * (p.kappa2 - 1))) +
    (Icc (alpha7 p) (alpha5 p)).indicator (fun _ => (1 : ℝ)) t /
      (5 * t * (1 - t / p.S)) *
      log (p.S^2 / ((p.kappa1 * p.S - p.S - p.kappa1 * t) *
        (p.kappa3 * p.S - p.S - p.kappa3 * t))) +
    (Icc (alpha5 p) (alpha8 p)).indicator (fun _ => (1 : ℝ)) t /
      (5 * t * (1 - t / p.S)) *
      log (p.S * (p.S - 1 - t) / (p.kappa1 * p.S - p.S - p.kappa1 * t)) +
    (Icc (alpha6 p) (alpha8 p)).indicator (fun _ => (1 : ℝ)) t /
      (5 * t * (1 - t / p.S)) *
      log (p.S / (p.kappa2 * p.S - p.S - p.kappa2 * t)) +
    (Icc (alpha8 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t /
      (5 * t * (1 - t / p.S)) * log (p.S - 1 - t) := by
  simp [xi2, xi2Weight, xi2Left, xi2Right, xi2Numerator, xi2Denominator,
    xi2Scale, Fin.sum_univ_succ]
  ring

theorem xi2_support_geometry (i : Fin 4) (j : Fin 9) :
    1 ≤ xi2Left (coupledRow i) j ∧
    xi2Left (coupledRow i) j ≤ xi2Right (coupledRow i) j ∧
    xi2Right (coupledRow i) j ≤ 3 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [xi2Left, xi2Right, alpha1, alpha2, alpha3, alpha5, alpha6, alpha7,
      alpha8, alpha9, coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem xi2_product_bounds (i : Fin 4) :
    0 < xi2Product (coupledRow i) ∧ xi2Product (coupledRow i) ≤ 1024 := by
  fin_cases i <;>
    norm_num [xi2Product, coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem xi2_right_denominator_positive (i : Fin 4) (j : Fin 9) :
    0 < xi2Denominator (coupledRow i) (xi2Right (coupledRow i) j) j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [xi2Right, xi2Denominator, xi2Product,
      alpha1, alpha2, alpha3, alpha5, alpha6, alpha7, alpha8, alpha9,
      coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem xi2_product_factors_positive (i : Fin 4) :
    0 < (coupledRow i).kappa1 * (coupledRow i).S - (coupledRow i).S -
      (coupledRow i).kappa1 * xi2Right (coupledRow i) 5 ∧
    0 < (coupledRow i).kappa3 * (coupledRow i).S - (coupledRow i).S -
      (coupledRow i).kappa3 * xi2Right (coupledRow i) 5 := by
  change 0 < (coupledRow i).kappa1 * (coupledRow i).S - (coupledRow i).S -
      (coupledRow i).kappa1 * alpha5 (coupledRow i) ∧
    0 < (coupledRow i).kappa3 * (coupledRow i).S - (coupledRow i).S -
      (coupledRow i).kappa3 * alpha5 (coupledRow i)
  fin_cases i <;>
    norm_num [alpha5, coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem xi2_denominator_positive (i : Fin 4) (j : Fin 9) {t : ℝ}
    (ht : t ∈ Icc (xi2Left (coupledRow i) j) (xi2Right (coupledRow i) j)) :
    0 < xi2Denominator (coupledRow i) t j := by
  have hg := coupled_geometry_bounds (coupledRow_geometry i)
  have hs : 0 ≤ (coupledRow i).s - 1 := by linarith [hg.1]
  have hk1 : 0 ≤ (coupledRow i).kappa1 := by
    have h := (coupledRow_geometry i).2.1
    linarith
  have hk2 : 0 ≤ (coupledRow i).kappa2 - 1 := by linarith [hg.2.2.1]
  have hk3 : 0 ≤ (coupledRow i).kappa3 - 1 := by linarith [hg.2.2.2.2.1]
  have hk2' : 0 ≤ (coupledRow i).kappa2 := by linarith only [hk2]
  have hk3' : 0 ≤ (coupledRow i).kappa3 := by linarith only [hk3]
  have hb := ht.2
  apply (xi2_right_denominator_positive i j).trans_le
  fin_cases j
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hb _) hk2
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hb _) hk3
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hb _) hs
  · exact le_rfl
  · have hp := xi2_product_factors_positive i
    have h1 := sub_le_sub_left (mul_le_mul_of_nonneg_left hb hk1)
      ((coupledRow i).kappa1 * (coupledRow i).S - (coupledRow i).S)
    have h2 := sub_le_sub_left (mul_le_mul_of_nonneg_left hb hk3')
      ((coupledRow i).kappa3 * (coupledRow i).S - (coupledRow i).S)
    change _ * _ ≤ _ * _
    exact mul_le_mul h1 h2 hp.2.le (hp.1.le.trans h1)
  · exact sub_le_sub_left (mul_le_mul_of_nonneg_left hb hk1) _
  · exact sub_le_sub_left (mul_le_mul_of_nonneg_left hb hk2') _
  · exact le_rfl

theorem xi2_numerator_positive (i : Fin 4) (j : Fin 9) {t : ℝ}
    (ht : t ∈ Icc (xi2Left (coupledRow i) j) (xi2Right (coupledRow i) j)) :
    0 < xi2Numerator (coupledRow i) t j := by
  have hgeom := xi2_support_geometry i j
  have ht0 : 0 < t := by linarith [hgeom.1, ht.1]
  have ht1 : 0 < t + 1 := by linarith
  fin_cases i <;> fin_cases j <;>
    norm_num [xi2Left, xi2Right, xi2Numerator, alpha1, alpha2, alpha3, alpha5,
      alpha6, alpha7, alpha8, alpha9, coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4] at ht ⊢ <;>
    first | positivity | linarith

theorem xi2_scale_positive (i : Fin 4) (j : Fin 9) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 3) : 0 < xi2Scale (coupledRow i) t j := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hS : 3 < (coupledRow i).S := by
    fin_cases i <;>
      norm_num [coupledRow, SecondFunctionalPositive.parameters,
        SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
        SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]
  unfold xi2Scale
  split_ifs
  · positivity
  · exact mul_pos (by positivity)
      (sub_pos.mpr ((div_lt_one (by linarith : 0 < (coupledRow i).S)).mpr
        (ht.2.trans_lt hS)))

theorem xi2_polynomials_continuous (p : SecondFunctionalParameters) (j : Fin 9) :
    Continuous (fun t => xi2Numerator p t j) ∧
    Continuous (fun t => xi2Denominator p t j) ∧
    Continuous (fun t => xi2Scale p t j) := by
  fin_cases j <;> simp only [xi2Numerator, xi2Denominator, xi2Scale] <;>
    norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceLT, if_true, if_false] <;>
    exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

theorem xi2_weight_continuous (i : Fin 4) (j : Fin 9) :
    ContinuousOn (xi2Weight (coupledRow i) j)
      (Icc (xi2Left (coupledRow i) j) (xi2Right (coupledRow i) j)) := by
  have hc := xi2_polynomials_continuous (coupledRow i) j
  have hg := xi2_support_geometry i j
  apply ((hc.1.continuousOn.div hc.2.1.continuousOn
    (fun t ht => (xi2_denominator_positive i j ht).ne')).log
      (fun t ht => (div_pos (xi2_numerator_positive i j ht)
        (xi2_denominator_positive i j ht)).ne')).div hc.2.2.continuousOn
  intro t ht
  exact (xi2_scale_positive i j ⟨hg.1.trans ht.1, ht.2.trans hg.2.2⟩).ne'

end WuPaper.R2Matrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
