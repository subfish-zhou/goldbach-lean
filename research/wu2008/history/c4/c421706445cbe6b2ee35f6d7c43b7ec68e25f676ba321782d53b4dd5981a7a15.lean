import WR2PsiCostsSuprema

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalJointTail SecondFunctionalGeometricMass
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open Wu04HighCoupledSupport
open scoped BigOperators
noncomputable section

theorem fourI_le_mass (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) : fourI p j ≤ fourMass p j :=
  phiSup_le (fun phi _ => (fourK_bounds p hp hs j phi).2)

theorem I20_le_mass (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : I20 p ≤ highMass20 p :=
  phiSup_le (fun phi _ => (K20_bounds p hp hs phi).2)

theorem I21_le_mass (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : I21 p ≤ highMass21 p :=
  phiSup_le (fun phi _ => (K21_bounds p hp hs phi).2)

theorem highMass_log_caps (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    highMass20 p ≤ U20 p * L p ∧ highMass21 p ≤ U21 p * L p := by
  obtain ⟨ha, haa, hab, _⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have ha0 : 0 < 1 / p.kappa3 := by linarith
  have hlow : 0 ≤ Real.log ((1 / p.kappa3) / (1 / p.kappa2)) :=
    Real.log_nonneg ((one_le_div (by linarith : 0 < 1 / p.kappa2)).2 haa)
  have h20 := selected_log_cap (2 : Fin 4) ha0 hab
  have h21 := selected_log_cap (4 : Fin 6) ha0 hab
  constructor
  · rw [OriginalBlocks.highMass20_blocks p hp hs]
    calc
      _ ≤ Real.log ((1 / p.kappa3) / (1 / p.kappa2)) *
          (Real.log ((1 / p.s) / (1 / p.kappa3)) ^ 4 /
            ((4 : ℕ).factorial * (1 / p.kappa3))) :=
        mul_le_mul_of_nonneg_left h20 hlow
      _ = _ := by norm_num [U20, L, HighUnitSource.unitLogCap20]; ring
  · rw [OriginalBlocks.highMass21_blocks p]
    calc
      _ ≤ Real.log ((1 / p.s) / (1 / p.kappa3)) ^ 6 /
          ((6 : ℕ).factorial * (1 / p.kappa3)) := h21
      _ = _ := by norm_num [U21, L, HighUnitSource.unitLogCap21]; ring

theorem original_highMass_le_U20 (i : Fin 4) :
    highMass20 (parameters i) + highMass21 (parameters i) ≤ U20 (parameters i) := by
  have hp := original_mother i
  have hs := original_s_ge_two i
  obtain ⟨ha, haa, hab, _⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have ha0 : 0 < 1 / (parameters i).kappa3 := by linarith
  have hg := Wu04CoupledCostProducer.original_ratios i
  have hA := hg.2.1.trans (Real.one_sub_inv_le_log_of_pos hg.1)
  have hl : 0 ≤ L (parameters i) := Real.log_nonneg ((one_le_div ha0).2 hab)
  have hlhi : L (parameters i) ≤ 1 / 2 :=
    (Real.log_le_sub_one_of_pos hg.2.2.1).trans hg.2.2.2
  have hsmall := Wu04CoupledCostProducer.small_high_caps ha0 hA hl hlhi
  have hsmall' :
      max (U20 (parameters i)) (U20 (parameters i) * L (parameters i) +
        max (U21 (parameters i)) (U21 (parameters i) * L (parameters i))) ≤
          U20 (parameters i) := by
    simpa only [U20, U21, L, HighUnitSource.unitLogCap20, HighUnitSource.unitLogCap21]
      using hsmall
  obtain ⟨h20, h21⟩ := highMass_log_caps (parameters i) hp hs
  have hinner := le_max_right (U21 (parameters i)) (U21 (parameters i) * L (parameters i))
  have houter := le_max_right (U20 (parameters i))
    (U20 (parameters i) * L (parameters i) +
      max (U21 (parameters i)) (U21 (parameters i) * L (parameters i)))
  linarith only [h20, h21, hinner, houter, hsmall']

theorem original_high_independent_maxima (i : Fin 4) :
    I20 (parameters i) + I21 (parameters i) ≤ U20 (parameters i) :=
  (add_le_add (I20_le_mass _ (original_mother i) (original_s_ge_two i))
    (I21_le_mass _ (original_mother i) (original_s_ge_two i))).trans
      (original_highMass_le_U20 i)

theorem original_lowerI_le_mass (i : Fin 4) (j : Fin 6) :
    lowerI (parameters i) j ≤ (4 / 7) * lowerMass (parameters i) j := by
  apply phiSup_le
  intro phi hphi
  rw [lowerK_eq _ (original_mother i) (original_s_ge_two i) j hphi]
  exact original_lower_mass_bound i j hphi

theorem original_remaining_independent_maxima (i : Fin 4) :
    (∑ j, lowerI (parameters i) j) + (∑ j, fourI (parameters i) j) +
      I20 (parameters i) + I21 (parameters i) ≤
        Wu04CoupledCostProducer.kernelCap (parameters i) := by
  have hl := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) =>
    original_lowerI_le_mass i j)
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    fourI_le_mass _ (original_mother i) (original_s_ge_two i) j)
  rw [← Finset.mul_sum] at hl
  have hh := original_high_independent_maxima i
  unfold Wu04CoupledCostProducer.kernelCap
  linarith only [hl, hf, hh]

theorem originalCost_le_existing_analytic_cap (i : Fin 4) :
    originalCost (parameters i) ≤ Omega3ElementaryFeedback.omegaCost (parameters i) +
      Wu04CoupledCostProducer.kernelCap (parameters i) := by
  have h9 : I9 (parameters i) ≤ Omega3ElementaryFeedback.omegaCost (parameters i) := by
    apply phiSup_le
    intro phi hphi
    exact Omega3ElementaryEnvelope.integral_le (Omega3ElementaryFeedback.original_gates i).1
      (Omega3ElementaryFeedback.original_gates i).2.1
      (Omega3ElementaryFeedback.original_gates i).2.2 hphi
  have hr := original_remaining_independent_maxima i
  unfold originalCost
  linarith only [h9, hr]

def firstLowerCap (j : Fin 6) : ℝ :=
  Wu04MainTail.cap * lowerMass row1 j -
    (if j = 2 then Wu04ThreeMass.gain else 0) -
    (if j = 3 then Wu04RecoverRectangle.gain + Wu04CurveMass.gain else 0)

theorem first_lowerI_le (j : Fin 6) : lowerI row1 j ≤ firstLowerCap j := by
  apply phiSup_le
  intro phi hphi
  rw [lowerK_eq row1 (original_mother 0) (original_s_ge_two 0) j hphi]
  unfold firstLowerCap
  by_cases hj : j = 3
  · subst j
    simp only [show (3 : Fin 6) ≠ 2 by decide, ite_false, ite_true, sub_zero]
    linarith only [Wu04CurveMass.fourth_kernel hphi]
  · by_cases ht : j = 2
    · subst j
      simp only [ite_true, show (2 : Fin 6) ≠ 3 by decide, ite_false, sub_zero]
      have hk := Wu04ThreeMass.third_kernel hphi
      have hm := mul_le_mul_of_nonneg_left Wu04ThreeMass.third_mass_paid
        (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
      unfold Wu04ThreeMass.gain
      nlinarith only [hk, hm]
    · simpa only [hj, ht, ite_false, sub_zero] using Wu04MainCost.first_lower_mass j hphi

theorem first_lower_independent_maxima :
    (∑ j, lowerI row1 j) ≤ Wu04MainTail.cap * (∑ j, lowerMass row1 j) -
      Wu04ThreeMass.gain - Wu04RecoverRectangle.gain - Wu04CurveMass.gain := by
  classical
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) =>
    first_lowerI_le j)
  simp only [firstLowerCap, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  linarith only [h]

theorem first_remaining_independent_maxima :
    (∑ j, lowerI row1 j) + (∑ j, fourI row1 j) + I20 row1 + I21 row1 ≤
      Wu04CurveCost.jointCap := by
  have hl := first_lower_independent_maxima
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    fourI_le_mass row1 (original_mother 0) (original_s_ge_two 0) j)
  have hh := original_high_independent_maxima 0
  change I20 row1 + I21 row1 ≤ U20 row1 at hh
  unfold Wu04CurveCost.jointCap Wu04RecoverCost.jointCap Wu04ThreeCost.jointCap
    Wu04MainProducer.jointCap
  linarith only [hl, hf, hh]

theorem first_originalCost_paid : originalCost row1 ≤ Wu04CurveCost.costCap := by
  have h9 : I9 row1 ≤ Wu04MainProducer.omegaCap - Wu04RecoverGammaMass.gain := by
    apply phiSup_le
    intro phi hphi
    exact Wu04RecoverGammaMass.first_omega hphi
  have hr := first_remaining_independent_maxima
  have hc : originalCost row1 ≤
      (Wu04MainProducer.omegaCap - Wu04RecoverGammaMass.gain) + Wu04CurveCost.jointCap := by
    unfold originalCost
    linarith only [h9, hr]
  have he := Wu04MainProducer.complete_cap_identity
  have hb := Wu04WholeCostPaid.complete_cap_paid
  unfold Wu04CurveCost.costCap Wu04CurveCost.jointCap Wu04RecoverComplete.costCap
    Wu04RecoverCost.costCap Wu04RecoverCost.jointCap Wu04ThreeCost.costCap
    Wu04ThreeCost.jointCap at *
  linarith only [hc, he, hb]

theorem first_original_publication_budget :
    5 * Wu04CurvePaid.publication + Wu04CurvePaid.slack ≤
      Wu08OriginalPsiRecovery.classicalNumerator row1 - 2 * originalCost row1 := by
  have hb := Wu04WholeReversePaid.first_classical
  have hc := first_originalCost_paid
  unfold Wu04CurvePaid.slack
  linarith only [hb, hc]

end
end WuPaper.R2PsiCosts
