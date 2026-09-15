import R2PsiCostsCaps
import Wu04RemainingStrongPaid

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Wu04RemainingCore
open SecondFunctionalFourSevenths SecondFunctionalJointTail SecondFunctionalGeometricMass
open scoped BigOperators
noncomputable section

def remainingLowerCap (i : Fin 3) (j : Fin 6) : ℝ :=
  Wu04MainTail.cap * lowerMass (row i) j -
    (if j = 2 then Wu04RemainingStrongThird.gain (row i) else 0) -
    (if j = 3 then Wu04RemainingStrongFourthMass.gain i else 0)

theorem remaining_lowerI_le (i : Fin 3) (j : Fin 6) :
    lowerI (row i) j ≤ remainingLowerCap i j := by
  apply phiSup_le
  intro phi hphi
  rw [lowerK_eq (row i) (original_mother i.succ) (original_s_ge_two i.succ) j hphi]
  unfold remainingLowerCap
  by_cases h2 : j = 2
  · subst j
    simpa only [ite_true, show (2 : Fin 6) ≠ 3 by decide, ite_false, sub_zero] using
      Wu04RemainingStrongThird.kernel_paid i hphi
  · by_cases h3 : j = 3
    · subst j
      simpa only [h2, ite_false, ite_true, sub_zero] using
        Wu04RemainingStrongFourthMass.kernel_paid i hphi
    · simpa only [h2, h3, ite_false, sub_zero] using Wu04RemainingLower.lower_paid i j hphi

theorem remaining_lower_independent_maxima (i : Fin 3) :
    (∑ j, lowerI (row i) j) ≤ Wu04MainTail.cap * (∑ j, lowerMass (row i) j) -
      Wu04RemainingStrongThird.gain (row i) - Wu04RemainingStrongFourthMass.gain i := by
  classical
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) =>
    remaining_lowerI_le i j)
  simpa only [remainingLowerCap, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem remaining_independent_maxima (i : Fin 3) :
    (∑ j, lowerI (row i) j) + (∑ j, fourI (row i) j) + I20 (row i) + I21 (row i) ≤
      Wu04RemainingCost.jointCore (row i) -
        Wu04RemainingStrongThird.gain (row i) - Wu04RemainingStrongFourthMass.gain i := by
  have hl := remaining_lower_independent_maxima i
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    fourI_le_mass (row i) (original_mother i.succ) (original_s_ge_two i.succ) j)
  have hh := original_high_independent_maxima i.succ
  change I20 (row i) + I21 (row i) ≤ Wu04HighCoupledSupport.U20 (row i) at hh
  unfold Wu04RemainingCost.jointCore
  linarith only [hl, hf, hh]

theorem remaining_originalCost_paid (i : Fin 3) :
    originalCost (row i) ≤ Wu04RemainingStrongCompleteCost.costCap i := by
  have h9 : I9 (row i) ≤
      Wu04MainTail.cap * Elementary.elementaryMomentOne 1
        (Wu04RemainingStrongGamma.lo i) (Wu04RemainingStrongGamma.hi i) -
          Wu04RemainingStrongGammaMass.gain i := by
    apply phiSup_le
    intro phi hphi
    exact Wu04RemainingStrongGammaMass.remaining_omega i hphi
  have hr := remaining_independent_maxima i
  have hc : originalCost (row i) ≤
      (Wu04MainTail.cap * Elementary.elementaryMomentOne 1
        (Wu04RemainingStrongGamma.lo i) (Wu04RemainingStrongGamma.hi i) -
          Wu04RemainingStrongGammaMass.gain i) +
      (Wu04RemainingCost.jointCore (row i) - Wu04RemainingStrongThird.gain (row i) -
        Wu04RemainingStrongFourthMass.gain i) := by
    unfold originalCost
    linarith only [h9, hr]
  have he := Wu04RemainingCost.complete_identity (row i)
    (original_mother i.succ) (original_s_ge_two i.succ)
  have ht := mul_le_mul_of_nonneg_left (Wu04RemainingEnvelope.polynomials_paid i).1
    (show 0 ≤ Wu04MainTail.cap by norm_num [Wu04MainTail.cap])
  have hf := (Wu04RemainingEnvelope.polynomials_paid i).2
  have hh := Wu04RemainingEnvelope.high_paid i
  have hb : Wu04RemainingCost.costCore (row i) ≤ Wu04RemainingEnvelope.costCap (row i) := by
    unfold Wu04RemainingCost.costCore Wu04RemainingEnvelope.costCap
    linarith only [ht, hf, hh]
  unfold Wu04RemainingStrongGamma.lo Wu04RemainingStrongGamma.hi at hc
  unfold Wu04RemainingStrongCompleteCost.costCap Wu04RemainingStrongPrefixCost.costCap
  linarith only [hc, he, hb]

theorem remaining_original_publication_budget (i : Fin 3) :
    5 * publication i + Wu04RemainingStrongPublication.slack i ≤
      Wu08OriginalPsiRecovery.classicalNumerator (row i) - 2 * originalCost (row i) := by
  have hb := Wu04RemainingStrongClassical.complete_paid i
  have hc := remaining_originalCost_paid i
  unfold Wu04RemainingStrongPublication.slack
  linarith only [hb, hc]

def fullPsi (p : SecondFunctionalParameters) : ℝ :=
  (Wu08OriginalPsiRecovery.classicalNumerator p - 2 * originalCost p) / 5

theorem first_fullPsi_lower :
    Wu04CurvePaid.publication + Wu04CurvePaid.slack / 5 ≤
      fullPsi SecondFunctionalParameters.row1 := by
  unfold fullPsi
  linarith only [first_original_publication_budget]

theorem remaining_fullPsi_lower (i : Fin 3) :
    publication i + Wu04RemainingStrongPublication.slack i / 5 ≤ fullPsi (row i) := by
  unfold fullPsi
  linarith only [remaining_original_publication_budget i]

end
end WuPaper.R2PsiCosts
