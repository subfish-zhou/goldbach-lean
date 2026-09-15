import Wu04RemainingEnvelope

namespace Wu04RemainingTail
open Wu2008DoubleSieve Set MeasureTheory Wu04RemainingCore
open SecondFunctionalJointTail SecondFunctionalGeometricMass SecondFunctionalFourSevenths
noncomputable section

/-- Pointwise form of the now-proved original-row global gate. -/
theorem lower_point (i : Fin 3) (j : Fin 6) {φ : ℝ} (hφ : 2≤φ) {t : Fin 3 → ℝ}
    (ht : t∈LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j) :
    LowerTripleContinuous.G φ t*continuousDensity t≤Wu04MainTail.cap*geometricWeight 1 t := by
  have cube := LowerTripleContinuous.D_subset_cube (original_compact i.succ) j ht
  have hp : 0<t 1 := by linarith [(cube 1 (mem_univ 1)).1]
  have gate := Wu04RemainingLower.original_gate i j ht
  have arg : 1/Wu04MainTail.cap≤(φ-(t 0+t 1+t 2))/t 1 := by
    apply (le_div_iff₀ hp).mpr
    linarith only [gate,hφ]
  have cp : 0<Wu04MainTail.cap := by norm_num [Wu04MainTail.cap]
  have hu : 1≤Wu04MainTail.cap*((φ-(t 0+t 1+t 2))/t 1) := by
    have hm := mul_le_mul_of_nonneg_left arg cp.le
    rwa [mul_one_div_cancel cp.ne'] at hm
  rw [LowerTripleContinuous.G_cube_literal hφ cube]
  have h := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (Wu04MainTail.buchstab_le hu) hp.le)
    (continuousDensity_nonneg cube)
  convert h using 1 <;> first | rfl | (unfold geometricWeight; ring)

/-- Analytic debit core: the E mass is paid once, and its complement is retained. -/
theorem subdomain_paid (i : Fin 3) (j : Fin 6) {E : Set (Fin 3 → ℝ)}
    (hE : MeasurableSet E)
    (hsub : E⊆LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j)
    {φ : ℝ} (hφ : 2≤φ) (harg : ∀ t∈E,3≤(φ-(t 0+t 1+t 2))/t 1) :
    LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1) (1/(row i).kappa2)
      (1/(row i).kappa3) (1/(row i).s) j φ≤Wu04MainTail.cap*lowerMass (row i) j-
      (Wu04MainTail.cap-Wu04ThreeTail.cap)*geometricMass 1 E := by
  classical
  have hc := LowerTripleContinuous.D_subset_cube (original_compact i.succ) j
  have hw := geometricWeight_integrable 1 hc
  have hi := (hw.const_mul Wu04MainTail.cap).sub
    ((hw.indicator hE).const_mul (Wu04MainTail.cap-Wu04ThreeTail.cap))
  have hpoint : ∀ t∈LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j,
      LowerTripleContinuous.G φ t*continuousDensity t≤
      Wu04MainTail.cap*geometricWeight 1 t-
        (Wu04MainTail.cap-Wu04ThreeTail.cap)*E.indicator (geometricWeight 1) t := by
    intro t ht
    by_cases he : t∈E
    · rw [indicator_of_mem he]
      have cube := hc ht
      have hp : 0<t 1 := by linarith [(cube 1 (mem_univ 1)).1]
      have h := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (Wu04ThreeTail.buchstab_le (harg t he)) hp.le)
        (continuousDensity_nonneg cube)
      rw [LowerTripleContinuous.G_cube_literal hφ cube]
      convert h using 1 <;> first | rfl | (unfold geometricWeight; ring)
    · rw [indicator_of_notMem he,mul_zero,sub_zero]
      exact lower_point i j hφ ht
  have hm := setIntegral_mono_on (LowerTripleContinuous.K_integrable (original_compact i.succ) j φ)
    hi (LowerTripleContinuous.D_measurable _ _ _ _ _ j) hpoint
  change E⊆LowerTripleContinuous.D (1/(SecondFunctionalPositive.parameters i.succ).S)
    (1/(SecondFunctionalPositive.parameters i.succ).kappa1) (1/(SecondFunctionalPositive.parameters i.succ).kappa2)
    (1/(SecondFunctionalPositive.parameters i.succ).kappa3) (1/(SecondFunctionalPositive.parameters i.succ).s) j at hsub
  simp only [Pi.sub_apply] at hm
  rw [integral_sub (hw.const_mul _) ((hw.indicator hE).const_mul _),
    integral_const_mul,integral_const_mul,setIntegral_indicator hE,inter_eq_right.mpr hsub] at hm
  exact hm

end
end Wu04RemainingTail
