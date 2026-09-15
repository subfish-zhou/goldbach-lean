import Wu04MainTail

namespace Wu04MainCost
open Wu2008DoubleSieve Wu04MainTail Set MeasureTheory
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalGeometricMass SecondFunctionalJointTail
open scoped BigOperators
noncomputable section

theorem first_lower_gate (j : Fin 6) {t : Fin 3 → ℝ}
    (ht : t ∈ LowerTripleContinuous.D (1/row1.S) (1/row1.kappa1)
      (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) j) :
    t 0 + (1+1/cap)*t 1 + t 2 ≤ 2 := by
  have hall : ∀ j : Fin 6, t ∈ LowerTripleContinuous.D (1/row1.S) (1/row1.kappa1)
      (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) j →
      t 0 + (1+1/cap)*t 1 + t 2 ≤ 2 := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
      LowerTripleContinuous.D, LowerTripleGrouped.bands,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    repeat' constructor
    all_goals rintro ⟨_, ht0, _, ht1, _, ht2, _, _⟩
    all_goals norm_num only [row1,cap] at *
    all_goals linarith
  exact hall j ht

theorem first_lower_mass (j : Fin 6) {phi : ℝ} (hphi : 2 ≤ phi) :
    LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) j phi ≤ cap * lowerMass row1 j := by
  have hsub := LowerTripleContinuous.D_subset_cube (original_compact 0) j
  have hw := geometricWeight_integrable 1 hsub
  have hk := LowerTripleContinuous.K_integrable (original_compact 0) j phi
  change (∫ t in _, LowerTripleContinuous.G phi t * continuousDensity t) ≤
    cap * ∫ t in _, geometricWeight 1 t
  rw [← integral_const_mul]
  apply setIntegral_mono_on hk (hw.const_mul _) (LowerTripleContinuous.D_measurable _ _ _ _ _ j)
  intro t ht
  have hc := hsub ht
  rw [LowerTripleContinuous.G_cube_literal hphi hc]
  have hp : 0 < t 1 := by linarith [(hc 1 (mem_univ 1)).1]
  have hg := first_lower_gate j ht
  have hu : 1 ≤ cap*((phi-(t 0+t 1+t 2))/t 1) := by
    have harg : 1/cap ≤ (phi-(t 0+t 1+t 2))/t 1 := by
      apply (le_div_iff₀ hp).2
      linarith only [hg,hphi]
    have hh := mul_le_mul_of_nonneg_left harg (by norm_num [cap] : 0 ≤ cap)
    norm_num [cap] at hh ⊢
    exact hh
  have hb := Wu04MainTail.buchstab_le hu
  have hd := continuousDensity_nonneg hc
  calc
    _ ≤ (cap/t 1)*continuousDensity t :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) hd
    _ = _ := by unfold geometricWeight; ring

theorem first_lower_sum {phi : ℝ} (hphi : 2 ≤ phi) :
    (∑ j : Fin 6, LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1)
      (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) j phi) ≤
      cap * ∑ j : Fin 6, lowerMass row1 j := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => first_lower_mass j hphi)

/-- The Γ9 kernel retains its second coordinate squared. -/
theorem omega_kernel {phi a b c : ℝ} (hphi : 2 ≤ phi)
    (ha : a ≤ 25/61) (hb : b ≤ 25/61) (hc : c ≤ 25/61)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) :
    omega3XIntegralKernel phi a b c ≤ cap*(1/(a*b^2*c)) := by
  have hg : a+(1+1/cap)*b+c ≤ 2 := by norm_num [cap] at *; linarith
  have harg : 1/cap ≤ (phi-a-b-c)/b := by
    apply (le_div_iff₀ hb0).2
    linarith only [hg,hphi]
  have hu := mul_le_mul_of_nonneg_left harg (by norm_num [cap] : 0 ≤ cap)
  norm_num [cap] at hu
  have h := Wu04MainTail.buchstab_le hu
  unfold omega3XIntegralKernel
  calc
    _ ≤ cap/(a*b^2*c) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by ring

/-- Complete original nested Γ9 domain, at every phi in its own true supremum. -/
theorem first_omega {phi : ℝ} (hphi : 2 ≤ phi) :
    omega3XIntegral row1.kappa3 row1.kappa1 phi ≤
      cap * Elementary.elementaryMomentOne 1 (1/row1.kappa1) (1/row1.kappa3) := by
  let lo : ℝ := 1/row1.kappa1
  let hi : ℝ := 1/row1.kappa3
  have hl : (1/10:ℝ) ≤ lo := by norm_num [lo,row1]
  have hl0 : (0:ℝ) < lo := by norm_num [lo,row1]
  have hlh : lo ≤ hi := by norm_num [lo,hi,row1]
  have hh : hi = 25/61 := by norm_num [hi,row1]
  have hinner (a : ℝ) (ha : a ∈ Icc lo hi) (b : ℝ) (hb : b ∈ Icc a hi) :
      (∫ c in b..hi, omega3XIntegralKernel phi a b c) ≤
        cap*(∫ c in b..hi, (1:ℝ)/(a*b^2*c)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb.2
      (omega3XIntegralKernel_intervalIntegrable (hl.trans ha.1)
        ((hl.trans ha.1).trans hb.1) hb.2)
      ((Omega3ElementaryRegularity.kernel_integrable (hl.trans ha.1)
        ((hl.trans ha.1).trans hb.1) hb.2).const_mul _)
    intro c hc
    exact omega_kernel hphi (hh ▸ ha.2) (hh ▸ hb.2) (hh ▸ hc.2)
      (hl0.trans_le ha.1) ((hl0.trans_le ha.1).trans_le hb.1)
      (((hl0.trans_le ha.1).trans_le hb.1).trans_le hc.1)
  have hmiddle (a : ℝ) (ha : a ∈ Icc lo hi) :
      (∫ b in a..hi, ∫ c in b..hi, omega3XIntegralKernel phi a b c) ≤
        cap*(∫ b in a..hi, ∫ c in b..hi, (1:ℝ)/(a*b^2*c)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha.2
      (omega3XIntegral_inner_intervalIntegrable (hl.trans ha.1) ha.2)
      ((Omega3ElementaryRegularity.inner_integrable (hl.trans ha.1) ha.2).const_mul _)
      (hinner a ha)
  calc
    _ ≤ cap*(∫ a in lo..hi, ∫ b in a..hi, ∫ c in b..hi, (1:ℝ)/(a*b^2*c)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hlh
        (omega3XIntegral_middle_intervalIntegrable hl hlh)
        ((Omega3ElementaryRegularity.middle_integrable hl hlh).const_mul _) hmiddle
    _ = _ := by rw [Omega3ElementaryMass.nested_eq_elementary hl0 hlh]

#print axioms first_lower_sum
#print axioms first_omega
end
end Wu04MainCost
