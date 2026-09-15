import MathlibNt.Wu2008DoubleSieve.GeoMassOriginalBlocksDomains

/-! All twelve original masses, without replacing M or evaluating higher ordered masses. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.OriginalBlocks
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

theorem lowerMass_zero_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    lowerMass p 0 = selectedOrderedMass (1 : Fin 2) (1/p.kappa1) (1/p.kappa2) *
      Real.log ((1/p.s)/(1/p.kappa2)) := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have hb : 0 < 1/p.kappa1 := by linarith
  have hc : 0 < 1/p.kappa2 := hb.trans_le hbc
  simpa only [pure_one hc (hce.trans hef)] using!
    mass_blocks_left (1 : Fin 2) hb hc _
      (lower_zero_domain (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s))

theorem lowerMass_one_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    lowerMass p 1 = Real.log ((1/p.kappa2)/(1/p.kappa1)) *
      selectedOrderedMass (0 : Fin 2) (1/p.kappa2) (1/p.kappa3) := by
  obtain ⟨ha,hab,hbc,_hce,_hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have hb : 0 < 1/p.kappa1 := by linarith
  have hc : 0 < 1/p.kappa2 := hb.trans_le hbc
  simpa only [pure_one hb hbc] using!
    mass_blocks_right (0 : Fin 2) hb hc _
      (lower_one_domain (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s))

theorem lowerMass_two_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    lowerMass p 2 = selectedOrderedMass (1 : Fin 2) (1/p.S) (1/p.kappa1) *
      Real.log ((1/p.s)/(1/p.kappa3)) := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have he : 0 < 1/p.kappa3 := ha0.trans_le (hab.trans (hbc.trans hce))
  simpa only [pure_one he hef] using!
    mass_blocks_left (1 : Fin 2) ha0 he _
      (lower_two_domain (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s)
        (hbc.trans hce))

theorem lowerMass_three_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : lowerMass p 3 = lowerThreeLog p := lowerMass_three p hp hs

theorem lowerMass_four_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    lowerMass p 4 = Real.log ((1/p.kappa1)/(1/p.S)) *
      selectedOrderedMass (0 : Fin 2) (1/p.kappa2) (1/p.s) := by
  obtain ⟨ha,hab,hbc,_hce,_hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have hc : 0 < 1/p.kappa2 := ha0.trans_le (hab.trans hbc)
  simpa only [pure_one ha0 hab] using!
    mass_blocks_right (0 : Fin 2) ha0 hc _
      (lower_four_domain (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) hbc)

theorem lowerMass_five_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : lowerMass p 5 = lowerFiveLog p := lowerMass_five p hp hs

theorem highMass20_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    highMass20 p = Real.log ((1/p.kappa3)/(1/p.kappa2)) *
      selectedOrderedMass (2 : Fin 4) (1/p.kappa3) (1/p.s) := by
  obtain ⟨ha,hab,hbc,hce,_hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have hc : 0 < 1/p.kappa2 := by linarith
  have he : 0 < 1/p.kappa3 := hc.trans_le hce
  simpa only [pure_one hc hce] using!
    mass_blocks_right (2 : Fin 4) hc he _
      (high_twenty_domain (1/p.kappa2) (1/p.kappa3) (1/p.s))

theorem highMass21_blocks (p : SecondFunctionalParameters) :
    highMass21 p = selectedOrderedMass (4 : Fin 6) (1/p.kappa3) (1/p.s) := by
  unfold highMass21 selectedOrderedMass
  rw [high_twenty_one_domain]

theorem fourMass_zero_blocks (p : SecondFunctionalParameters) :
    fourMass p 0 = selectedOrderedMass (2 : Fin 4) (1/p.kappa2) (1/p.kappa3) := by
  change geometricMass 2 (FourPrimeContinuous.D16 _ _) = _
  rw [four_sixteen_domain]
  rfl

theorem fourMass_one_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    fourMass p 1 = selectedOrderedMass (2 : Fin 3) (1/p.kappa2) (1/p.kappa3) *
      Real.log ((1/p.s)/(1/p.kappa3)) := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have hc : 0 < 1/p.kappa2 := by linarith
  have he : 0 < 1/p.kappa3 := hc.trans_le hce
  simpa only [pure_one he hef] using!
    mass_blocks_left (2 : Fin 3) hc he _
      (four_seventeen_domain (1/p.kappa2) (1/p.kappa3) (1/p.s))

theorem fourMass_two_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    fourMass p 2 = pureOrderedMass 2 (1/p.kappa2) (1/p.kappa3) *
      selectedOrderedMass (0 : Fin 2) (1/p.kappa3) (1/p.s) := by
  obtain ⟨ha,hab,hbc,hce,_hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have hc : 0 < 1/p.kappa2 := by linarith
  have he : 0 < 1/p.kappa3 := hc.trans_le hce
  exact mass_blocks_right (0 : Fin 2) hc he _
    (four_eighteen_domain (1/p.kappa2) (1/p.kappa3) (1/p.s))

theorem fourMass_three_blocks (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    fourMass p 3 = Real.log ((1/p.kappa2)/(1/p.kappa1)) *
      selectedOrderedMass (1 : Fin 3) (1/p.kappa3) (1/p.s) := by
  obtain ⟨ha,hab,hbc,hce,_hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have hb : 0 < 1/p.kappa1 := by linarith
  have he : 0 < 1/p.kappa3 := hb.trans_le (hbc.trans hce)
  simpa only [pure_one hb hbc] using!
    mass_blocks_right (1 : Fin 3) hb he _
      (four_nineteen_domain (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) hce)

/-- The original total, with all twelve identities and precisely the original multiplicities.
The ordered integrals on the right are the shared literal integrals, not supplied formulas. -/
theorem M_blocks_exact (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    let a := 1/p.S
    let b := 1/p.kappa1
    let c := 1/p.kappa2
    let e := 1/p.kappa3
    let f := 1/p.s
    SecondFunctionalJointTail.M p =
      (selectedOrderedMass (1 : Fin 2) b c * Real.log (f/c) +
        Real.log (c/b) * selectedOrderedMass (0 : Fin 2) c e +
        selectedOrderedMass (1 : Fin 2) a b * Real.log (f/e) +
        lowerThreeLog p +
        Real.log (b/a) * selectedOrderedMass (0 : Fin 2) c f + lowerFiveLog p) +
      ((Real.log (e/c) * selectedOrderedMass (2 : Fin 4) e f +
        selectedOrderedMass (4 : Fin 6) e f) +
       (selectedOrderedMass (2 : Fin 4) c e +
        selectedOrderedMass (2 : Fin 3) c e * Real.log (f/e) +
        pureOrderedMass 2 c e * selectedOrderedMass (0 : Fin 2) e f +
        Real.log (c/b) * selectedOrderedMass (1 : Fin 3) e f)) := by
  dsimp only
  rw [M_two_rows_exact p hp hs, lowerMass_zero_blocks p hp hs,
    lowerMass_one_blocks p hp hs, lowerMass_two_blocks p hp hs,
    lowerMass_four_blocks p hp hs, highMass20_blocks p hp hs, highMass21_blocks p]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  erw [fourMass_zero_blocks p, fourMass_one_blocks p hp hs,
    fourMass_two_blocks p hp hs, fourMass_three_blocks p hp hs]
  ring

/-- Every original integral in the exact total is absolutely integrable. -/
theorem original_masses_integrable (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    (∀ j : Fin 6, IntegrableOn (geometricWeight 1)
      (LowerTripleContinuous.D (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j)) ∧
    IntegrableOn (geometricWeight 3) (massDomain20 (1/p.kappa2) (1/p.kappa3) (1/p.s)) ∧
    IntegrableOn (geometricWeight 4) (massDomain21 (1/p.kappa3) (1/p.s)) ∧
    (∀ j : Fin 4, IntegrableOn (geometricWeight 2)
      (massDomainFour (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) j)) :=
  mother_mass_integrable p hp hs

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.OriginalBlocks
