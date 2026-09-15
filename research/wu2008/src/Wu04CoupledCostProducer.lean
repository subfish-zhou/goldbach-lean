import Wu04HighCoupledSupport
import Wu08OriginalPsiRecovery
import MathlibNt.Wu2008DoubleSieve.Omega3ElementaryFeedback

namespace Wu04CoupledCostProducer
open Wu2008DoubleSieve Wu04HighCoupledSupport
open SecondFunctionalParameters SecondFunctionalPositive
open SecondFunctionalJointTail SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass
open ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

/-- Pure algebra for the already-paid logarithmic caps; no evaluation of logs. -/
theorem small_high_caps {a A l : ℝ} (ha : 0 < a)
    (hA : 1/30 ≤ A) (hl : 0 ≤ l) (hlhi : l ≤ 1/2) :
    max (A*l^3/(24*a))
      (A*l^3/(24*a)*l + max (l^5/(720*a)) (l^5/(720*a)*l)) ≤
        A*l^3/(24*a) := by
  have hA0 : 0 ≤ A := by linarith
  have hU : 0 ≤ A*l^3/(24*a) := by positivity
  have hV : 0 ≤ l^5/(720*a) := by positivity
  have hVl : l^5/(720*a)*l ≤ l^5/(720*a) :=
    mul_le_of_le_one_right hV (by linarith)
  rw [max_eq_left hVl]
  apply max_le le_rfl
  have hsq : l^2 ≤ 15*A := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hsq (pow_nonneg hl 3)
  have hhalf : l^5/(720*a) ≤ (A*l^3/(24*a))/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 720*a)).2
    have he : (A*l^3/(24*a))/2*(720*a) = 15*A*l^3 := by
      field_simp
      ring
    rw [he]
    nlinarith only [hp]
  have hUl : A*l^3/(24*a)*l ≤ (A*l^3/(24*a))/2 := by
    have hh := mul_le_mul_of_nonneg_left hlhi hU
    linarith only [hh]
  linarith only [hhalf, hUl]

theorem original_separation (i : Fin 4) : Separated (parameters i) := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [Separated, row1, row2, row3, row4]

/-- Rational endpoint facts at the four already-fixed published parameters. -/
theorem original_ratios (i : Fin 4) :
    0 < (1/(parameters i).kappa3)/(1/(parameters i).kappa2) ∧
    (1 : ℝ)/30 ≤ 1 - ((1/(parameters i).kappa3)/(1/(parameters i).kappa2))⁻¹ ∧
    0 < (1/(parameters i).s)/(1/(parameters i).kappa3) ∧
    (1/(parameters i).s)/(1/(parameters i).kappa3) - 1 ≤ (1 : ℝ)/2 := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [row1, row2, row3, row4]

/-- The whole unit+legal high payload is paid by the J20 cap alone. This does
not delete the other terms: support separation and their proved masses pay them. -/
theorem original_high_le_U20 (i : Fin 4) (phi : ℝ) :
    highKernel (parameters i) phi ≤ U20 (parameters i) := by
  have hp := original_mother i
  have hs := original_s_ge_two i
  obtain ⟨ha, haa, hab, _hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have ha0 : 0 < 1/(parameters i).kappa3 := by linarith
  have hg := original_ratios i
  have hA := (hg.2.1).trans (Real.one_sub_inv_le_log_of_pos hg.1)
  have hl : 0 ≤ L (parameters i) := Real.log_nonneg
    ((one_le_div ha0).2 hab)
  have hlhi : L (parameters i) ≤ 1/2 :=
    (Real.log_le_sub_one_of_pos hg.2.2.1).trans hg.2.2.2
  have hsmall := small_high_caps ha0 hA hl hlhi
  have h := high_coupled_cap (parameters i) hp hs (original_separation i) phi
  apply h.trans
  simpa only [U20, U21, L, HighUnitSource.unitLogCap20, HighUnitSource.unitLogCap21] using hsmall

/-- Explicit rational first-row payment, on every real phi, from log x <= x-1.
No quadrature, phi mesh, optimizer, new Taylor order, or printed cost is used. -/
theorem first_U20_rational : U20 row1 ≤ (207 : ℝ)/8318750 := by
  have hl0 : 0 ≤ Real.log ((61 : ℝ)/55) := Real.log_nonneg (by norm_num)
  have hA : Real.log ((145 : ℝ)/122) ≤ 23/122 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 145/122)
    linarith only [hh]
  have hl : Real.log ((61 : ℝ)/55) ≤ 6/55 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 61/55)
    linarith only [hh]
  have hp := pow_le_pow_left₀ hl0 hl 3
  have hm := mul_le_mul hA hp (pow_nonneg hl0 3) (by norm_num : (0 : ℝ) ≤ 23/122)
  have hd := div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 24*(25/61))
  norm_num [U20, HighUnitSource.unitLogCap20, row1] at hd ⊢
  exact hd

theorem first_high_rational (phi : ℝ) :
    highKernel row1 phi ≤ (207 : ℝ)/8318750 :=
  (original_high_le_U20 0 phi).trans first_U20_rational

noncomputable def kernelCap (p : SecondFunctionalParameters) : ℝ :=
  (4/7)*(∑ j : Fin 6, lowerMass p j) + (∑ j : Fin 4, fourMass p j) + U20 p

/-- Both original nonunit families, every lower triple, and both units remain
in the actual kernel being bounded; a common phi is used before the comparison. -/
theorem original_kernel_majorant (i : Fin 4) {phi : ℝ} (hphi : 2 ≤ phi) :
    SecondFunctionalCoupled.kernel (parameters i) phi ≤ kernelCap (parameters i) := by
  have hl := original_lower_sum_bound i hphi
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    four_mass_bound (parameters i) (original_mother i) (original_s_ge_two i) phi j)
  have hh := original_high_le_U20 i phi
  unfold SecondFunctionalCoupled.kernel kernelCap highKernel at *
  linarith only [hl, hf, hh]

/-- An exact comparison with the previously paid whole-phi analytic cap. -/
theorem kernelCap_eq_old_minus (p : SecondFunctionalParameters) :
    kernelCap p = analyticCap p - highMass20 p - highMass21 p - U21 p := by
  unfold kernelCap analyticCap U20 U21
  ring

/-- Integral-free form of the new cap; all moments are existing explicit
logarithmic primitives, not unevaluated phi maximizations. -/
noncomputable def elementaryKernelCap (p : SecondFunctionalParameters) : ℝ :=
  Elementary.elementaryMass p - (3/7)*elementaryLowerMass p -
    Real.log ((1/p.kappa3)/(1/p.kappa2))/2 *
      Elementary.elementaryMomentOne 2 (1/p.kappa3) (1/p.s) -
    Elementary.elementaryMomentOne 4 (1/p.kappa3) (1/p.s)/24 + U20 p

theorem kernelCap_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    kernelCap p = elementaryKernelCap p := by
  obtain ⟨ha, haa, hab, _hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have ha0 : 0 < 1/p.kappa3 := by linarith
  have h20 := OriginalBlocks.highMass20_blocks p hp hs
  have h21 := OriginalBlocks.highMass21_blocks p
  rw [FullReduction.selectedOrderedMass_eq_log (2 : Fin 4) ha0 hab] at h20
  rw [FullReduction.selectedOrderedMass_eq_log (4 : Fin 6) ha0 hab] at h21
  norm_num at h20 h21
  have he2 := Elementary.logMoment_one_eq 2 ha0 hab
  have he4 := Elementary.logMoment_one_eq 4 ha0 hab
  simp only [one_div] at he2 he4
  rw [he2] at h20
  rw [he4] at h21
  rw [kernelCap_eq_old_minus, analyticCap_eq_elementary p hp hs]
  unfold elementaryCap elementaryKernelCap
  rw [h20, h21]
  unfold U20 U21
  simp only [one_div, div_inv_eq_mul]
  ring

/-- No I/K interface debt: both pointwise majorants have genuine proofs. -/
theorem original_cost_majorant (i : Fin 4) :
    coupledCostMass (parameters i) ≤
      Omega3ElementaryFeedback.omegaCost (parameters i) + kernelCap (parameters i) := by
  apply Wu08OriginalPsiRecovery.original_cost_of_pointwise
  · intro phi hphi
    exact Omega3ElementaryEnvelope.integral_le (Omega3ElementaryFeedback.original_gates i).1
      (Omega3ElementaryFeedback.original_gates i).2.1
      (Omega3ElementaryFeedback.original_gates i).2.2 hphi
  · intro phi hphi
    exact original_kernel_majorant i hphi

/-- Actual positive-delta source with all nine feedback coordinates unchanged. -/
theorem actual_four_rows (i : Fin 4) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) :
    Wu08OriginalPsiRecovery.classicalNumerator (parameters i)/5 -
      2*(Omega3ElementaryFeedback.omegaCost (parameters i) + kernelCap (parameters i)) /
        (5*(1-2*δ)) + coupledFeedback (parameters i) (actualNine δ) ≤
      wuImprovementLimit true δ (parameters i).s := by
  apply Wu08OriginalPsiRecovery.quantitative_source_producer (coupledRow_geometry i)
  · intro phi hphi
    exact Omega3ElementaryEnvelope.integral_le (Omega3ElementaryFeedback.original_gates i).1
      (Omega3ElementaryFeedback.original_gates i).2.1
      (Omega3ElementaryFeedback.original_gates i).2.2 hphi
  · intro phi hphi
    exact original_kernel_majorant i hphi
  · exact hd
  · exact hh

/-- First-row numerical high payment inside the real complete coupled cost. -/
theorem first_cost_rational_high :
    coupledCostMass row1 ≤ Omega3ElementaryFeedback.omegaCost row1 +
      (4/7)*(∑ j : Fin 6, lowerMass row1 j) +
      (∑ j : Fin 4, fourMass row1 j) + (207 : ℝ)/8318750 := by
  have h := original_cost_majorant 0
  change coupledCostMass row1 ≤ Omega3ElementaryFeedback.omegaCost row1 + kernelCap row1 at h
  have hu := first_U20_rational
  unfold kernelCap at h
  linarith only [h, hu]

#print axioms original_high_le_U20
#print axioms first_high_rational
#print axioms original_cost_majorant
#print axioms actual_four_rows
#print axioms first_cost_rational_high
end
end Wu04CoupledCostProducer
