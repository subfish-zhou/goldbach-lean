import Wu04ThreePaid

namespace Wu04RecoverRectangle
open Wu2008DoubleSieve Set MeasureTheory Real
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalJointTail SecondFunctionalGeometricMass
open SharpLogRecurrence JointLogTotalComparison
noncomputable section
open Classical

def a : ℝ := 1/row1.S
def b : ℝ := 1/row1.kappa1
def c : ℝ := 1/row1.kappa2
def f : ℝ := 1/row1.s
/-- Forced u=3 at the two original upper endpoints x=b, z=f. -/
def r : ℝ := (2-b-f)/4
def R : Set (Fin 3 → ℝ) := continuousRectangle ![a,b,c] ![b,r,f]

theorem endpoint_geometry : 0<a ∧ a≤b ∧ b<r ∧ r<c ∧ c≤f := by
  norm_num [a,b,c,f,r,row1]

theorem R_literal {t : Fin 3 → ℝ} : t∈R ↔
    a≤t 0 ∧ t 0≤b ∧ b≤t 1 ∧ t 1≤r ∧ c≤t 2 ∧ t 2≤f := by
  simp only [R,continuousRectangle,mem_pi,mem_univ,forall_const,Fin.forall_fin_succ,
    Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ,mem_Icc]
  tauto

theorem R_measurable : MeasurableSet R := by
  unfold R continuousRectangle
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem R_subset : R ⊆ LowerTripleContinuous.D (1/row1.S) (1/row1.kappa1)
    (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) 3 := by
  intro t ht
  obtain ⟨h0,h0',h1,h1',h2,h2'⟩ := R_literal.mp ht
  change a≤t 0 ∧ t 0≤b ∧ b≤t 1 ∧ t 1≤c ∧ c≤t 2 ∧ t 2≤f ∧ t 0≤t 1 ∧ t 1≤t 2
  have hrc := endpoint_geometry.2.2.2.1.le
  exact ⟨h0,h0',h1,h1'.trans hrc,h2,h2',h0'.trans h1,(h1'.trans hrc).trans h2⟩

theorem R_argument {phi : ℝ} (hphi : 2≤phi) {t : Fin 3 → ℝ} (ht : t∈R) :
    3≤(phi-(t 0+t 1+t 2))/t 1 := by
  obtain ⟨_,h0,h1,h1',_,h2⟩ := R_literal.mp ht
  have hb : 0<b := by norm_num [b,row1]
  apply (le_div_iff₀ (hb.trans_le h1)).2
  unfold r at h1'
  linarith

theorem R_mass_exact : geometricMass 1 R = log (b/a)*(1/b-1/r)*log (f/c) := by
  exact triple_rectangle_mass endpoint_geometry.1
    (endpoint_geometry.1.trans_le endpoint_geometry.2.1)
    (by norm_num [c,row1]) endpoint_geometry.2.1 endpoint_geometry.2.2.1.le
    endpoint_geometry.2.2.2.2

def massLower : ℝ := Wu04FactorEnvelopes.lower (b/a)*(1/b-1/r)*Wu04FactorEnvelopes.lower (f/c)

theorem massLower_pos : 0<massLower := by
  norm_num [massLower,a,b,c,f,r,row1,Wu04FactorEnvelopes.lower,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,lowerLog]

theorem R_mass_paid : massLower≤geometricMass 1 R := by
  rw [R_mass_exact]
  have hx := Wu04FactorEnvelopes.lower_le_log (by norm_num [a,b,row1] : 1≤b/a)
  have hz := Wu04FactorEnvelopes.lower_le_log (by norm_num [c,f,row1] : 1≤f/c)
  have hx0 : 0≤Wu04FactorEnvelopes.lower (b/a) := by
    norm_num [a,b,row1,Wu04FactorEnvelopes.lower,
      Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,lowerLog]
  have hz0 : 0≤Wu04FactorEnvelopes.lower (f/c) := by
    norm_num [c,f,row1,Wu04FactorEnvelopes.lower,
      Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,lowerLog]
  have hd : 0≤1/b-1/r := by norm_num [b,r,f,row1]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hx hd) hz hz0 (mul_nonneg (hx0.trans hx) hd)

/-- Actual-domain subtraction retains the old cap everywhere outside the paid subdomain. -/
theorem subdomain_payment (j : Fin 6) {E : Set (Fin 3 → ℝ)} (hE : MeasurableSet E)
    (hsub : E ⊆ LowerTripleContinuous.D (1/row1.S) (1/row1.kappa1)
      (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) j)
    {phi : ℝ} (hphi : 2≤phi)
    (harg : ∀ t∈E, 3≤(phi-(t 0+t 1+t 2))/t 1) :
    LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) j phi ≤ Wu04MainTail.cap*lowerMass row1 j-
        (Wu04MainTail.cap-Wu04ThreeTail.cap)*geometricMass 1 E := by
  have hc := LowerTripleContinuous.D_subset_cube (original_compact 0) j
  have hw := geometricWeight_integrable 1 hc
  have hi := (hw.const_mul Wu04MainTail.cap).sub
    ((hw.indicator hE).const_mul (Wu04MainTail.cap-Wu04ThreeTail.cap))
  have hm := setIntegral_mono_on (LowerTripleContinuous.K_integrable (original_compact 0) j phi)
    hi (LowerTripleContinuous.D_measurable _ _ _ _ _ j) (fun t ht => by
      have htC := hc ht
      have hp : 0<t 1 := by linarith [(htC 1 (mem_univ 1)).1]
      rw [LowerTripleContinuous.G_cube_literal hphi htC]
      simp only [Pi.sub_apply]
      by_cases he : t∈E
      · rw [indicator_of_mem he]
        have hb := Wu04ThreeTail.buchstab_le (harg t he)
        have hb' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le)
          (continuousDensity_nonneg htC)
        calc
          _ ≤ Wu04ThreeTail.cap / t 1 * continuousDensity t := hb'
          _ = _ := by unfold geometricWeight; ring
      · rw [indicator_of_notMem he, mul_zero, sub_zero]
        have hg := Wu04MainCost.first_lower_gate j ht
        have harg' : 1/Wu04MainTail.cap≤(phi-(t 0+t 1+t 2))/t 1 := by
          apply (le_div_iff₀ hp).2
          linarith only [hg,hphi]
        have hh := mul_le_mul_of_nonneg_left harg' (by norm_num [Wu04MainTail.cap] : 0≤Wu04MainTail.cap)
        have hb := Wu04MainTail.buchstab_le (show 1≤Wu04MainTail.cap*((phi-(t 0+t 1+t 2))/t 1) by
          norm_num [Wu04MainTail.cap] at hh ⊢
          exact hh)
        calc
          _ ≤ (Wu04MainTail.cap/t 1)*continuousDensity t :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) (continuousDensity_nonneg htC)
          _ = _ := by unfold geometricWeight; ring)
  change E ⊆ LowerTripleContinuous.D (1/(parameters 0).S) (1/(parameters 0).kappa1)
    (1/(parameters 0).kappa2) (1/(parameters 0).kappa3) (1/(parameters 0).s) j at hsub
  simp only [Pi.sub_apply] at hm
  rw [integral_sub (hw.const_mul _) ((hw.indicator hE).const_mul _),
    integral_const_mul,integral_const_mul,setIntegral_indicator hE,inter_eq_right.mpr hsub] at hm
  exact hm

def gain : ℝ := (Wu04MainTail.cap-Wu04ThreeTail.cap)*massLower

theorem gain_pos : 0<gain := mul_pos (sub_pos.mpr Wu04ThreeTail.cap_lt_main) massLower_pos

theorem fourth_kernel {phi : ℝ} (hphi : 2≤phi) :
    LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) 3 phi ≤ Wu04MainTail.cap*lowerMass row1 3-gain := by
  have hk := subdomain_payment 3 R_measurable R_subset hphi (fun _ ht => R_argument hphi ht)
  have hm := mul_le_mul_of_nonneg_left R_mass_paid (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
  unfold gain
  linarith only [hk,hm]

end
end Wu04RecoverRectangle
