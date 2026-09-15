import Wu04RemainingStrongClassical

namespace Wu04RemainingStrongThird
open Wu2008DoubleSieve Real Set MeasureTheory Wu04RemainingCore
open SecondFunctionalFourSevenths SecondFunctionalGeometricMass SecondFunctionalJointTail
open SecondFunctionalGeometricMass.Elementary Wu04RemainingEnvelope Wu04FullPsiMass
noncomputable section

theorem endpoint_gate (i : Fin 3) : 5/(row i).kappa1+1/(row i).s≤2 := by
  revert i
  simp only [row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4]

theorem argument (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) {t : Fin 3 → ℝ}
    (ht : t∈LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) 2) :
    3≤(φ-(t 0+t 1+t 2))/t 1 := by
  have hc := LowerTripleContinuous.D_subset_cube (original_compact i.succ) 2 ht
  have hp : 0<t 1 := by linarith [(hc 1 (mem_univ 1)).1]
  change 1/(row i).S≤t 0 ∧ t 0≤1/(row i).kappa1 ∧ 1/(row i).S≤t 1 ∧
    t 1≤1/(row i).kappa1 ∧ 1/(row i).kappa3≤t 2 ∧ t 2≤1/(row i).s ∧ t 0≤t 1 ∧ t 1≤t 2 at ht
  apply (le_div_iff₀ hp).mpr
  have hg : 5*(1/(row i).kappa1)+1/(row i).s≤2 := by
    convert endpoint_gate i using 1
    ring
  linarith only [hφ,hg,ht.2.1,ht.2.2.2.1,ht.2.2.2.2.2.1]

theorem mass_exact (i : Fin 3) : lowerMass (row i) 2 =
    w (row i)*((row i).S-(row i).kappa1*(1+x (row i))) := by
  obtain ⟨ha,hab,_,_,_,_⟩ := LowerTripleContinuous.mother_compact_parameters (row i)
    (original_mother i.succ) (original_s_ge_two i.succ)
  have hp : 0<1/(row i).S := by linarith
  rw [OriginalBlocks.lowerMass_two_blocks (row i) (original_mother i.succ) (original_s_ge_two i.succ),
    FullReduction.selectedOrderedMass_eq_log (1:Fin 2) hp hab]
  norm_num only [Fin.val_one,Nat.factorial,Nat.cast_one,one_mul,div_one]
  rw [logMoment_zero_eq 1 hp hab]
  unfold elementaryMomentZero x w
  simp only [momentPolynomial,Nat.factorial,Nat.cast_one,mul_one,one_div_one_div]
  simp only [one_div,div_inv_eq_mul]
  ring

def massLower (p : SecondFunctionalParameters) : ℝ := lw p*(p.S-p.kappa1*(1+ux p))
def gain (p : SecondFunctionalParameters) : ℝ := (Wu04MainTail.cap-Wu04ThreeTail.cap)*massLower p

theorem factor_nonneg (i : Fin 3) : 0≤(row i).S-(row i).kappa1*(1+ux (row i)) := by
  revert i
  simp only [row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [ux,SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4,
    Wu04FactorEnvelopes.upper,Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,JointLogTotalComparison.V]

theorem mass_paid (i : Fin 3) : massLower (row i)≤lowerMass (row i) 2 := by
  rw [mass_exact]
  have hl := log_bounds i
  have g : MotherPair.AnalyticParameters (row i) := (ActualNineFeedback.coupledRow_geometry i.succ).1
  have hk : 0≤(row i).kappa1 := by linarith [g.two_lt_s,g.mother.s_le_kappa3,g.mother.kappa3_lt_kappa2,g.mother.kappa2_lt_kappa1]
  have hm := mul_le_mul_of_nonneg_left hl.2.1 hk
  apply mul_le_mul hl.2.2.2.2.2.2.1 _ (factor_nonneg i)
    (hl.2.2.2.2.2.2.2.2.2.2.2.trans hl.2.2.2.2.2.2.1)
  linarith only [hm]

theorem kernel_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1) (1/(row i).kappa2)
      (1/(row i).kappa3) (1/(row i).s) 2 φ≤Wu04MainTail.cap*lowerMass (row i) 2-gain (row i) := by
  have h := Wu04RemainingTail.subdomain_paid i 2 (LowerTripleContinuous.D_measurable _ _ _ _ _ 2)
    (Subset.refl _) hφ (fun _ ht => argument i hφ ht)
  have hm := mul_le_mul_of_nonneg_left (mass_paid i) (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
  unfold gain
  change _≤Wu04MainTail.cap*lowerMass (row i) 2-
    (Wu04MainTail.cap-Wu04ThreeTail.cap)*lowerMass (row i) 2 at h
  linarith only [h,hm]
end
end Wu04RemainingStrongThird
