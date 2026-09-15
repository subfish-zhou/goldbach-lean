import MathlibNt.Wu2008DoubleSieve.FourSeventhsKernel
import MathlibNt.Wu2008DoubleSieve.GeoMassElementaryFeedback

/-! The proved whole-parameter cap has an exact integral-free mass expression. -/
namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass SecondFunctionalGeometricMass.Elementary
open SecondFunctionalJointTail
open scoped BigOperators

noncomputable def elementaryLowerMass (p : SecondFunctionalParameters) : ℝ :=
  let a := 1/p.S
  let b := 1/p.kappa1
  let c := 1/p.kappa2
  let e := 1/p.kappa3
  let f := 1/p.s
  Real.log (f/c) * elementaryMomentZero 1 b c +
    Real.log (c/b) * elementaryMomentOne 0 c e +
    Real.log (f/e) * elementaryMomentZero 1 a b + lowerThreeLog p +
    Real.log (b/a) * elementaryMomentOne 0 c f + lowerFiveLog p

theorem lowerMass_sum_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 6, lowerMass p j) = elementaryLowerMass p := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  erw [OriginalBlocks.lowerMass_zero_blocks p hp hs,
    OriginalBlocks.lowerMass_one_blocks p hp hs, OriginalBlocks.lowerMass_two_blocks p hp hs,
    OriginalBlocks.lowerMass_three_blocks p hp hs, OriginalBlocks.lowerMass_four_blocks p hp hs,
    OriginalBlocks.lowerMass_five_blocks p hp hs]
  rw [FullReduction.selectedOrderedMass_eq_log (1 : Fin 2) hb0 hbc,
    FullReduction.selectedOrderedMass_eq_log (0 : Fin 2) hc0 hce,
    FullReduction.selectedOrderedMass_eq_log (1 : Fin 2) ha0 hab,
    FullReduction.selectedOrderedMass_eq_log (0 : Fin 2) hc0 (hce.trans hef)]
  norm_num only [Fin.val_one, Fin.val_zero, Nat.factorial]
  rw [logMoment_zero_eq 1 hb0 hbc, logMoment_one_eq 0 hc0 hce,
    logMoment_zero_eq 1 ha0 hab, logMoment_one_eq 0 hc0 (hce.trans hef)]
  norm_num [elementaryLowerMass]
  ring

noncomputable def elementaryCap (p : SecondFunctionalParameters) : ℝ :=
  elementaryMass p - (3/7) * elementaryLowerMass p +
    HighUnitSource.unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
    HighUnitSource.unitLogCap21 (1/p.kappa3) (1/p.s)

theorem analyticCap_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) : analyticCap p = elementaryCap p := by
  unfold elementaryCap
  rw [← M_elementary p hp hs, ← lowerMass_sum_eq_elementary p hp hs]
  unfold analyticCap SecondFunctionalJointTail.M
  ring

theorem original_jointSup_elementary (i : Fin 4) :
    SecondFunctionalCoupled.jointSup (SecondFunctionalPositive.parameters i) ≤
      elementaryCap (SecondFunctionalPositive.parameters i) := by
  rw [← analyticCap_eq_elementary _ (original_mother i) (original_s_ge_two i)]
  exact original_jointSup_bound i

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
