import Wu04ThreeTail

namespace Wu04ThreeMass
open Wu2008DoubleSieve Real Set MeasureTheory
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass SecondFunctionalJointTail
open SecondFunctionalGeometricMass.Elementary
open SharpLogRecurrence JointLogTotalComparison Wu04FullPsiMass
noncomputable section

/-- The third source domain is indexed 2, not the fourth domain named lowerThreeLog. -/
theorem third_argument {phi : ℝ} (hphi : 2≤phi) {t : Fin 3 → ℝ}
    (ht : t ∈ LowerTripleContinuous.D (1/row1.S) (1/row1.kappa1)
      (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) 2) :
    (3801:ℝ)/1100 ≤ (phi-(t 0+t 1+t 2))/t 1 := by
  have hs := ht
  change 1/row1.S≤t 0 ∧ t 0≤1/row1.kappa1 ∧ 1/row1.S≤t 1 ∧
    t 1≤1/row1.kappa1 ∧ 1/row1.kappa3≤t 2 ∧ t 2≤1/row1.s ∧ t 0≤t 1 ∧ t 1≤t 2 at hs
  norm_num only [row1] at hs
  obtain ⟨h0,h0',h1,h1',h2,h2',_,_⟩ := hs
  have hp : 0<t 1 := by linarith
  apply (le_div_iff₀ hp).2
  linarith

theorem third_kernel {phi : ℝ} (hphi : 2≤phi) :
    LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) 2 phi ≤ Wu04ThreeTail.cap*lowerMass row1 2 := by
  have hsub := LowerTripleContinuous.D_subset_cube (original_compact 0) 2
  have hw := geometricWeight_integrable 1 hsub
  have hk := LowerTripleContinuous.K_integrable (original_compact 0) 2 phi
  change (∫ t in _, LowerTripleContinuous.G phi t*continuousDensity t) ≤
    Wu04ThreeTail.cap*∫ t in _, geometricWeight 1 t
  rw [← integral_const_mul]
  apply setIntegral_mono_on hk (hw.const_mul _) (LowerTripleContinuous.D_measurable _ _ _ _ _ 2)
  intro t ht
  have hc := hsub ht
  rw [LowerTripleContinuous.G_cube_literal hphi hc]
  have hp : 0<t 1 := by linarith [(hc 1 (mem_univ 1)).1]
  have hb := Wu04ThreeTail.buchstab_le (show 3≤(phi-(t 0+t 1+t 2))/t 1 by
    have h := third_argument hphi ht
    linarith)
  calc
    _ ≤ (Wu04ThreeTail.cap/t 1)*continuousDensity t :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) (continuousDensity_nonneg hc)
    _ = _ := by unfold geometricWeight; ring

/-- Exact original full triangular mass; the selected v denominator stays squared. -/
theorem third_mass_exact : lowerMass row1 2 =
    w row1*(row1.S-row1.kappa1*(1+x row1)) := by
  rw [OriginalBlocks.lowerMass_two_blocks row1 (original_mother 0) (original_s_ge_two 0),
    FullReduction.selectedOrderedMass_eq_log (1:Fin 2)
      (by norm_num [row1] : 0<1/row1.S) (by norm_num [row1] : 1/row1.S≤1/row1.kappa1)]
  norm_num only [Fin.val_one,Nat.factorial,Nat.cast_one,one_mul,div_one]
  rw [logMoment_zero_eq 1 (by norm_num [row1] : 0<1/row1.S)
    (by norm_num [row1] : 1/row1.S≤1/row1.kappa1)]
  unfold elementaryMomentZero x w
  simp only [momentPolynomial,Nat.factorial,Nat.cast_one,mul_one,one_div_one_div]
  simp only [one_div,div_inv_eq_mul]
  ring

def massLower : ℝ := Wu04WholeCostPaid.lw*(row1.S-row1.kappa1*(1+Wu04WholeCostPaid.ux))

theorem massLower_pos : 0<massLower := by
  norm_num [massLower,row1,Wu04WholeCostPaid.lw,Wu04WholeCostPaid.ux,
    Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,V,lowerLog,upperLog]

theorem third_mass_paid : massLower≤lowerMass row1 2 := by
  rw [third_mass_exact]
  obtain ⟨_,hxu,_,_,_,_,hwl,_⟩ := Wu04WholeCostPaid.first_log_bounds
  have hw0 : 0≤Wu04WholeCostPaid.lw := by
    norm_num [Wu04WholeCostPaid.lw,Wu04FactorEnvelopes.lower,
      Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,lowerLog]
  have ha0 : 0≤row1.S-row1.kappa1*(1+Wu04WholeCostPaid.ux) := by
    norm_num [row1,Wu04WholeCostPaid.ux,Wu04FactorEnvelopes.upper,
      Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,V,lowerLog,upperLog]
  have ha : row1.S-row1.kappa1*(1+Wu04WholeCostPaid.ux) ≤ row1.S-row1.kappa1*(1+x row1) := by
    norm_num only [row1] at *
    linarith only [hxu]
  exact mul_le_mul hwl ha ha0 (hw0.trans hwl)

def gain : ℝ := (Wu04MainTail.cap-Wu04ThreeTail.cap)*massLower

theorem gain_pos : 0<gain := mul_pos (sub_pos.mpr Wu04ThreeTail.cap_lt_main) massLower_pos

end
end Wu04ThreeMass
