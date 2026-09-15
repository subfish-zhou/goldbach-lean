import Wu04CurveVolume

namespace Wu04CurveMass
open Wu2008DoubleSieve Set MeasureTheory Real
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalFourSevenths
open SecondFunctionalJointTail Wu04CurveGeometry Wu04CurveVolume
noncomputable section

/-- Only the fixed original-endpoint expression is used. -/
def massLower : ℝ := (Wu04RecoverRectangle.b-Wu04RecoverRectangle.a)*
  (Wu04RecoverRectangle.f-Wu04RecoverRectangle.c)^2/
  (8*Wu04RecoverRectangle.b*rc^2*Wu04RecoverRectangle.f)

def gain : ℝ := (Wu04MainTail.cap-Wu04ThreeTail.cap)*massLower

theorem massLower_exact : massLower = (3083449705 : ℝ)/492493138192 := by
  norm_num [massLower,rc,Wu04RecoverRectangle.a,Wu04RecoverRectangle.b,
    Wu04RecoverRectangle.c,Wu04RecoverRectangle.f,row1]

theorem gain_exact : gain = (24672971652343 : ℝ)/1274308265318825088 := by
  rw [gain,massLower_exact,Wu04ThreeTail.cap_value]
  norm_num [Wu04MainTail.cap]

theorem massLower_pos : 0<massLower := by rw [massLower_exact]; norm_num

theorem gain_pos : 0<gain := by rw [gain_exact]; norm_num

/-- Paid from the genuine selected-square weight and actual product volume. -/
theorem T_mass_paid : massLower ≤ geometricMass 1 T := by
  have hi : IntegrableOn (fun _ : Fin 3 → ℝ =>
      1/(Wu04RecoverRectangle.b*rc^2*Wu04RecoverRectangle.f)) T :=
    integrableOn_const (by rw [T_volume]; exact ENNReal.ofReal_ne_top)
  have h := setIntegral_mono_on hi (geometricWeight_integrable 1 T_cube)
    T_measurable (fun _ ht => weight_lower ht)
  rw [setIntegral_const,T_volume_real] at h
  change _ ≤ geometricMass 1 T at h
  convert h using 1
  simp only [smul_eq_mul]
  unfold massLower
  ring

theorem union_mass : geometricMass 1 (Wu04RecoverRectangle.R ∪ T) =
    geometricMass 1 Wu04RecoverRectangle.R + geometricMass 1 T := by
  unfold geometricMass
  exact setIntegral_union R_T_disjoint T_measurable
    (geometricWeight_integrable 1 (Wu04RecoverRectangle.R_subset.trans
      (LowerTripleContinuous.D_subset_cube (original_compact 0) 3)))
    (geometricWeight_integrable 1 T_cube)

/-- A single subtraction on the disjoint union, never a sum of two full K bounds. -/
theorem fourth_kernel {phi : ℝ} (hphi : 2≤phi) :
    LowerTripleContinuous.K (1/row1.S) (1/row1.kappa1) (1/row1.kappa2)
      (1/row1.kappa3) (1/row1.s) 3 phi ≤ Wu04MainTail.cap*lowerMass row1 3-
      Wu04RecoverRectangle.gain-gain := by
  have hsub : Wu04RecoverRectangle.R ∪ T ⊆ LowerTripleContinuous.D (1/row1.S)
      (1/row1.kappa1) (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) 3 :=
    union_subset Wu04RecoverRectangle.R_subset T_subset
  have hk := Wu04RecoverRectangle.subdomain_payment 3
    (Wu04RecoverRectangle.R_measurable.union T_measurable) hsub hphi
    (fun t ht => ht.elim (fun hr => Wu04RecoverRectangle.R_argument hphi hr)
      (fun ht => T_argument hphi ht))
  rw [union_mass] at hk
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add Wu04RecoverRectangle.R_mass_paid T_mass_paid)
    (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
  unfold Wu04RecoverRectangle.gain gain
  linarith only [hk,hm]

end
end Wu04CurveMass
