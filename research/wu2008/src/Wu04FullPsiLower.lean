import Wu04FullPsiEndpoints
import Wu04FullPsiClassical
import Wu04FullPsiCostCertificate

namespace Wu04FullPsiLower
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open SecondFunctionalParameters SecondFunctionalPositive
open Wu08OriginalPsiRecovery Wu04FullPsiSharp Wu04FullPsiEndpoints
open Wu04FullPsiMass Wu04FullPsiCostCertificate SharpLogRecurrence JointLogTotalComparison
noncomputable section

def classicalLower (p : SecondFunctionalParameters) : ℝ :=
  lowerJ p.s p.S + lowerJ p.kappa3 p.kappa1 -
  2*upperL p.S - 2*upperL p.kappa1 - Wu04FullPsiClassical.lSmallUpper p.kappa2

theorem original_classical_gates (i : Fin 4) :
    2 < (parameters i).s ∧ (parameters i).s ≤ (parameters i).S ∧
    2 ≤ (parameters i).S*(1-1/(parameters i).s) ∧
    2 < (parameters i).kappa3 ∧ (parameters i).kappa3 ≤ (parameters i).kappa1 ∧
    2 ≤ (parameters i).kappa1*(1-1/(parameters i).kappa3) ∧
    3 ≤ (parameters i).S ∧ 3 ≤ (parameters i).kappa1 ∧
    2 < (parameters i).kappa2 ∧ (parameters i).kappa2 ≤ 3 := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [row1,row2,row3,row4]

theorem four_classical_lower (i : Fin 4) :
    classicalLower (parameters i) ≤ classicalNumerator (parameters i) := by
  obtain ⟨hs,hsS,hg,hk,hk1,hg1,hS,h1,h2,h23⟩ := original_classical_gates i
  have hj := lower_j hs hsS hg
  have hj1 := lower_j hk hk1 hg1
  have hl := upper_l hS
  have hl1 := upper_l h1
  have hl2 := Wu04FullPsiClassical.l_small_upper h2 h23
  unfold classicalLower classicalNumerator
  linarith only [hj,hj1,hl,hl1,hl2]

/-- Full analytic lower certificate at all four fixed original rows. -/
theorem four_numerator_lower (i : Fin 4) :
    classicalLower (parameters i)-2*fullCostPolynomial (parameters i) ≤
    classicalNumerator (parameters i)-2*coupledCostMass (parameters i) := by
  have hb := four_classical_lower i
  have hc := original_cost_polynomial i
  linarith only [hb,hc]

/-- Actual positive-delta consumer, with no continuity-at-zero assumption. -/
theorem four_actual_inputs (i : Fin 4) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    classicalLower (parameters i)/5 -
      2*fullCostPolynomial (parameters i)/(5*(1-2*δ)) +
      coupledFeedback (parameters i) (actualNine δ) ≤
      wuImprovementLimit true δ (parameters i).s := by
  have h := Wu04CoupledCostProducer.actual_four_rows i hd hh
  rw [full_cost_polynomial _ (SecondFunctionalFourSevenths.original_mother i)
    (SecondFunctionalFourSevenths.original_s_ge_two i)] at h
  have hb := four_classical_lower i
  linarith only [h,hb]

def firstClassicalCertificate : ℝ :=
  rationalJ row1.s row1.S + rationalJ row1.kappa3 row1.kappa1 -
  2*rationalL row1.S - 2*rationalL row1.kappa1 +
  2*lowerLog (20/19)-V (10/9)

theorem first_small_L_bound :
    Wu04FullPsiClassical.lSmallUpper row1.kappa2 ≤ -2*lowerLog (20/19)+V (10/9) := by
  have h1 := log_lower (by norm_num : (1:ℝ)≤20/19)
  have h2 := log_le_V (by norm_num : (1:ℝ)≤10/9)
  have hi : Real.log ((19:ℝ)/20) = -Real.log (20/19) := by
    rw [show (19:ℝ)/20=(20/19)⁻¹ by norm_num, Real.log_inv]
  have hj : Real.log ((9:ℝ)/10) = -Real.log (10/9) := by
    rw [show (9:ℝ)/10=(10/9)⁻¹ by norm_num, Real.log_inv]
  norm_num [Wu04FullPsiClassical.lSmallUpper,row1]
  rw [hi,hj]
  linarith only [h1,h2]

theorem first_classical_certificate : firstClassicalCertificate ≤ classicalLower row1 := by
  have hJ := rationalJ_le (A:=row1.S) (B:=row1.s)
    (by norm_num [row1]) (by norm_num [row1]) (by norm_num [c,row1])
  have hK := rationalJ_le (A:=row1.kappa1) (B:=row1.kappa3)
    (by norm_num [row1]) (by norm_num [row1]) (by norm_num [c,row1])
  have hL := upperL_le (A:=row1.S) (by norm_num [row1])
  have hM := upperL_le (A:=row1.kappa1) (by norm_num [row1])
  have hN := first_small_L_bound
  unfold firstClassicalCertificate classicalLower
  linarith only [hJ,hK,hL,hM,hN]

theorem first_classical_rational : (214652:ℝ)/1000000 ≤ classicalNumerator row1 := by
  have hr : (214652:ℝ)/1000000 ≤ firstClassicalCertificate := by
    norm_num [firstClassicalCertificate,rationalJ,rationalL,c,d,Wu04FullPsiSharp.e,f,row1,lowerLog,V,upperLog]
  exact (hr.trans first_classical_certificate).trans (four_classical_lower 0)

/-- Genuine unconditional bound for the complete original numerator, not a high-only cap. -/
theorem first_full_rational : (52808:ℝ)/1000000 ≤
    classicalNumerator row1-2*coupledCostMass row1 := by
  have hb := first_classical_rational
  have hc := first_cost_rational
  linarith only [hb,hc]

/-- The admitted first row includes the entire feedback and delta debit. -/
theorem first_actual_rational {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    (214652:ℝ)/5000000 - 2*(80922/1000000)/(5*(1-2*δ)) +
    coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s := by
  have h := original_logs_actual_lower (coupledRow_geometry 0) hd hh
  change classicalNumerator row1/5 - 2*coupledCostMass row1/(5*(1-2*δ)) +
    coupledFeedback row1 (actualNine δ) ≤ wuImprovementLimit true δ row1.s at h
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left first_cost_rational (by norm_num : (0:ℝ)≤2))
    (show 0 ≤ 5*(1-2*δ) by linarith)
  have hb := first_classical_rational
  linarith only [h,hc,hb]

/-- Exact residual of THIS certificate, not a counterexample to the actual target. -/
theorem first_certificate_residual :
    5*(15826357:ℝ)/1000000000-52808/1000000 = 5264757/200000000 ∧
    0 < (5264757:ℝ)/200000000 := by norm_num

/-- What remains in the literal target: two genuine, nonnegative analytic slacks. -/
theorem first_actual_residual_identity :
    classicalNumerator row1-2*coupledCostMass row1-5*(15826357:ℝ)/1000000000 =
    (classicalNumerator row1-214652/1000000) +
    2*(80922/1000000-coupledCostMass row1)-5264757/200000000 := by ring

theorem first_residual_slacks_nonnegative :
    0 ≤ classicalNumerator row1-214652/1000000 ∧
    0 ≤ 80922/1000000-coupledCostMass row1 :=
  ⟨sub_nonneg.mpr first_classical_rational, sub_nonneg.mpr first_cost_rational⟩

#print axioms four_actual_inputs
#print axioms first_classical_rational
#print axioms first_full_rational
#print axioms first_actual_rational
#print axioms first_actual_residual_identity
end
end Wu04FullPsiLower
