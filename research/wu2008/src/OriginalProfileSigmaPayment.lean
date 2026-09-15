import OriginalSigmaKernelPayment

namespace OriginalProfileSigmaPayment
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open scoped Interval BigOperators
noncomputable section

/-- The parameter-dependent genuine sigma kernel is continuous on its full original domain. -/
theorem original_sigma_continuous :
    ContinuousOn (fun t : ℝ => sigma 3 (t+2) (t+1)) (uIcc 1 3) := by
  have hq : IntervalIntegrable (fun v : ℝ => log (v-1)/v) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by norm_num)
    intro v hv
    have hv0 : v≠0 := by linarith [hv.1]
    have hv1 : v-1≠0 := by linarith [hv.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hc := intervalIntegral.continuousOn_primitive_interval' hq
    (show (3:ℝ)∈uIcc 3 5 from left_mem_uIcc)
  have hm : MapsTo (fun t : ℝ => t+2) (uIcc 1 3) (uIcc 3 5) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht ⊢
    constructor <;> linarith [ht.1,ht.2]
  have hp := hc.comp (continuousOn_id.add continuousOn_const) hm
  have hl : ContinuousOn (fun t : ℝ => log (t+1)*log ((t+2)/3)) (uIcc 1 3) := by
    rw [uIcc_of_le (by norm_num)]
    intro t ht
    have h1 : t+1≠0 := by linarith [ht.1]
    have h2 : (t+2)/3≠0 := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  apply (hl.sub hp).congr
  intro t ht
  rw [uIcc_of_le (by norm_num)] at ht
  have ht0 : 0<t+1 := by linarith [ht.1]
  have ht2 : 0<t+2 := by linarith [ht.1]
  have hab : (3:ℝ)≤t+2 := by linarith [ht.1]
  have hir := (reciprocal_continuous (by norm_num : (0:ℝ)<3) hab).intervalIntegrable (μ := volume)
  have hiq : IntervalIntegrable (fun v : ℝ => log (v-1)/v) volume 3 (t+2) := by
    apply hq.mono_set
    rw [uIcc_of_le hab,uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc le_rfl (by linarith [ht.2])
  have he : sigma 3 (t+2) (t+1) =
      ∫ v in (3:ℝ)..(t+2), log (t+1)*(1/v)-log (v-1)/v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    have hv1 : v-1≠0 := by linarith [hv.1]
    dsimp only
    rw [log_div ht0.ne' hv1]
    ring
  dsimp only [Pi.sub_apply, Function.comp_apply, Pi.add_apply, id]
  rw [he, intervalIntegral.integral_sub (hir.const_mul _) hiq,
    intervalIntegral.integral_const_mul, integral_one_div_of_pos (by norm_num) ht2]

/-- Finite endpoint numerator, retaining every one of the original nine cells. -/
def aNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*(sigmaPrimitive (upperNode k)-sigmaPrimitive (upperLeft k))

/-- Exact feedback normalization: D0 is the original sigma(3,5,4), not omitted. -/
def aLower (z : Fin 9 → ℝ) : ℝ := aNumerator z/(1-D0)

theorem aNumerator_eq_integral (z : Fin 9 → ℝ) :
    aNumerator z = ∫ t in (1:ℝ)..3, nineProfile z t*sigmaWeight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (sigmaWeight_continuous (by norm_num) (by norm_num))]
  apply Finset.sum_congr rfl
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [sigmaWeight_integral (by linarith [hb.1] : 0<cellLeft 1 k) hb.2.1,he]

theorem aNumerator_nonneg {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) : 0≤aNumerator z := by
  rw [aNumerator_eq_integral]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  apply mul_nonneg (nineProfile_nonneg hz t)
  unfold sigmaWeight
  have ht0 : 0<t := by linarith [ht.1]
  positivity

/-- An unconditional full-domain payment of the actual profile for any nonnegative original data. -/
theorem aLower_le_aProfile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    aLower z ≤ aProfile (nineProfile z) := by
  rw [aLower,aProfile_eq,aNumerator_eq_integral]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  have hp := nineProfile_integrable z
  have hlow := hp.mul_continuousOn (sigmaWeight_continuous (by norm_num) (by norm_num))
  have hhigh := (profile_div_integrable hp).mul_continuousOn original_sigma_continuous
  apply intervalIntegral.integral_mono_on (by norm_num) hlow hhigh
  intro t ht
  have ht0 : 0<t := by linarith [ht.1]
  have h := mul_le_mul_of_nonneg_left (sigma_floor_le ht.1)
    (div_nonneg (nineProfile_nonneg hz t) ht0.le)
  convert h using 1 <;> first | rfl | skip
  unfold sigmaWeight sigmaFloor
  field_simp

/-- Fully finite endpoint bound. This explicitly uses D0 >= 1/10, rather than deleting feedback. -/
def aFiniteLower (z : Fin 9 → ℝ) : ℝ := aNumerator z/(1-(1:ℝ)/10)

theorem aFiniteLower_le_aLower {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    aFiniteLower z ≤ aLower z := by
  apply div_le_div_of_nonneg_left (aNumerator_nonneg hz) (sub_pos.mpr D0_lt_one)
  linarith [D0_floor]

theorem aFiniteLower_le_aProfile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    aFiniteLower z ≤ aProfile (nineProfile z) :=
  (aFiniteLower_le_aLower hz).trans (aLower_le_aProfile hz)

theorem original_aLower_paid :
    aLower NineFeedbackStrength.originalH ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  aLower_le_aProfile CoupledIntegralRecovery.originalH_nonneg

theorem original_aFiniteLower_paid :
    aFiniteLower NineFeedbackStrength.originalH ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  aFiniteLower_le_aProfile CoupledIntegralRecovery.originalH_nonneg

end
end OriginalProfileSigmaPayment
