import MathlibNt.Wu2008DoubleSieve.HighSixPhase5LogBounds
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource

namespace Wu2008DoubleSieve.HighSixPhase5
open Real Set MeasureTheory
noncomputable section

def jLog (v : ℝ) : ℝ := (179/50)*log v/((v+1)*(179/50-1-v))
def lowerPrimitive (v : ℝ) : ℝ :=
  (3330663700/68782062249)*v+(387091900/2547483787)*v^2/2-
  (43240145000/68782062249)*v^3/3+(1404000000/2547483787)*v^4/4-
  (8450000000/68782062249)*v^5/5
def upperPrimitive (v : ℝ) : ℝ := (v-1)^2/4-(v-1)^3/(6*q)

theorem lowerPoly_integral : (∫ v in q..r, lowerPoly v) = 23865281381837/906685144566318 := by
  have h : (∫ v in q..r, lowerPoly v) = lowerPrimitive r-lowerPrimitive q := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := lowerPrimitive)
    · intro x _
      have h1 := (hasDerivAt_id x).const_mul (3330663700/68782062249)
      have h2 := (((hasDerivAt_id x).pow 2).const_mul (387091900/2547483787)).div_const 2
      have h3 := (((hasDerivAt_id x).pow 3).const_mul (43240145000/68782062249)).div_const 3
      have h4 := (((hasDerivAt_id x).pow 4).const_mul (1404000000/2547483787)).div_const 4
      have h5 := (((hasDerivAt_id x).pow 5).const_mul (8450000000/68782062249)).div_const 5
      convert (((h1.add h2).sub h3).add h4).sub h5 using 1 <;>
        first | rfl | (dsimp [lowerPoly,d,e,q,r]; ring)
    · exact (by unfold lowerPoly; fun_prop : Continuous lowerPoly).intervalIntegrable _ _
  rw [h]
  norm_num [lowerPrimitive,q,r]

theorem upperPoly_integral : (∫ v in (1 : ℝ)..q, upperPoly v) = 377883/41299375 := by
  have h : (∫ v in (1 : ℝ)..q, upperPoly v) = upperPrimitive q-upperPrimitive 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := upperPrimitive)
    · intro x _
      have h0 := (hasDerivAt_id x).sub_const 1
      convert ((h0.pow 2).div_const 4).sub ((h0.pow 3).div_const (6*q)) using 1 <;>
        first | rfl | (dsimp [upperPoly]; ring)
    · exact (by unfold upperPoly; fun_prop : Continuous upperPoly).intervalIntegrable _ _
  rw [h]
  norm_num [upperPrimitive,q]

theorem baseLog_continuous {a b : ℝ} (ha : 1 ≤ a) : ContinuousOn baseLog (Icc a b) := by
  unfold baseLog
  apply ContinuousOn.div
  · exact continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1])
  · fun_prop
  · intro x hx; linarith [hx.1]

theorem combined_continuous : ContinuousOn combined (Icc q r) := by
  unfold combined
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · fun_prop
    · exact continuousOn_id.log (fun x hx => by change x ≠ 0; norm_num [q] at hx; linarith [hx.1])
  · fun_prop
  · intro x hx
    have h1 : 0 < 179/50-1-x := by norm_num [r] at hx; linarith [hx.2]
    have h2 : 0 < x+1 := by norm_num [q] at hx; linarith [hx.1]
    positivity

theorem combined_integral_lower :
    23865281381837/906685144566318 ≤ ∫ v in q..r, combined v := by
  rw [← lowerPoly_integral]
  apply intervalIntegral.integral_mono_on (by norm_num [q,r])
    ((by unfold lowerPoly; fun_prop : Continuous lowerPoly).intervalIntegrable _ _)
    (ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (show q ≤ r by norm_num [q,r])] using combined_continuous))
  exact fun v hv => combined_lower hv

theorem baseLog_integral_upper : (∫ v in (1 : ℝ)..q, baseLog v) ≤ 377883/41299375 := by
  rw [← upperPoly_integral]
  apply intervalIntegral.integral_mono_on (by norm_num [q])
    (ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (show (1 : ℝ) ≤ q by norm_num [q])] using baseLog_continuous (b := q) le_rfl))
    ((by unfold upperPoly; fun_prop : Continuous upperPoly).intervalIntegrable _ _)
  exact fun v hv => baseLog_upper hv

/-- The affine substitution acts on the literal original J. -/
theorem original_J_change :
    (∫ u in (1-1/(13/5) : ℝ)..(1-1/(179/50)),
      log ((179/50)*u-1)/(u*(1-u))) = ∫ v in q..r, jLog v := by
  calc
    _ = ∫ u in (1-1/(13/5) : ℝ)..(1-1/(179/50)), (179/50)*jLog ((179/50)*u-1) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num)] at hu
      have hu0 : u ≠ 0 := by norm_num at hu; linarith [hu.1]
      have hu1 : 1-u ≠ 0 := by norm_num at hu; linarith [hu.2]
      have hu3 : 179-u*179 ≠ 0 := by intro he; apply hu1; linarith
      unfold jLog
      field_simp
      ring_nf
      field_simp [hu3]
      ring
    _ = (179/50)*(∫ u in (1-1/(13/5) : ℝ)..(1-1/(179/50)), jLog ((179/50)*u-1)) :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by
      have h := intervalIntegral.smul_integral_comp_mul_sub (f := jLog)
        (a := (1-1/(13/5) : ℝ)) (b := 1-1/(179/50)) (179/50) 1
      norm_num [q,r,smul_eq_mul] at h ⊢
      exact h

/-- The A difference is shifted before it is combined with J. -/
theorem original_A_change :
    (∫ v in (2 : ℝ)..(179/50-1), log (v-1)/v) = ∫ v in (1 : ℝ)..r, baseLog v := by
  calc
    _ = ∫ v in (2 : ℝ)..(179/50-1), baseLog (v-1) := by
      apply intervalIntegral.integral_congr
      intro v _
      simp [baseLog]
    _ = _ := by
      have h := intervalIntegral.integral_comp_sub_right (f := baseLog)
        (a := (2 : ℝ)) (b := 179/50-1) 1
      simpa only [r, show (2 : ℝ)-1=1 by norm_num, show (179/50 : ℝ)-1-1=79/50 by norm_num] using h

theorem original_combined :
    firstFunctionalGainPsiOne (13/5) (179/50) =
      (∫ v in q..r, combined v)-(∫ v in (1 : ℝ)..q, baseLog v)-
        omega3XIntegralEnvelope (13/5) (179/50) := by
  have hbase1 : IntervalIntegrable baseLog volume 1 q :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (show (1 : ℝ) ≤ q by norm_num [q])] using baseLog_continuous (b := q) le_rfl)
  have hbase2 : IntervalIntegrable baseLog volume q r :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (show q ≤ r by norm_num [q,r])] using baseLog_continuous (b := r) (show 1 ≤ q by norm_num [q]))
  have hj : ContinuousOn jLog (Icc q r) := by
    unfold jLog
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_id.log (fun x hx => by change x ≠ 0; norm_num [q] at hx; linarith [hx.1]))
    · fun_prop
    · intro x hx
      have h1 : 0 < 179/50-1-x := by norm_num [r] at hx; linarith [hx.2]
      have h2 : 0 < x+1 := by norm_num [q] at hx; linarith [hx.1]
      positivity
  have hji : IntervalIntegrable jLog volume q r :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (show q ≤ r by norm_num [q,r])] using hj)
  have hid : (∫ v in q..r, combined v) = (1/2)*(∫ v in q..r, jLog v)-(∫ v in q..r, baseLog v) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hji.const_mul _) hbase2]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num [q,r])] at hv
    have h1 : 179/50-1-v ≠ 0 := by norm_num [r] at hv; linarith [hv.2]
    have h2 : v+1 ≠ 0 := by norm_num [q] at hv; linarith [hv.1]
    have h3 : 129-v*50 ≠ 0 := by intro he; apply h1; linarith
    unfold combined jLog baseLog
    field_simp
    ring_nf
    field_simp [h3]
    ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hbase1 hbase2
  unfold firstFunctionalGainPsiOne
  rw [original_J_change,original_A_change]
  linarith only [hid,hadd]

/-- The exact positive gain comes from the original PsiOne, with no sign premise. -/
theorem psi_lower :
    (3629895479136046171/1363514967405501300000 : ℝ) ≤
      firstFunctionalGainPsiOne (13/5) (179/50) := by
  rw [original_combined]
  linarith only [combined_integral_lower,baseLog_integral_upper,envelope_upper]

theorem psi_positive : 0 < firstFunctionalGainPsiOne (13/5) (179/50) := by
  exact lt_of_lt_of_le (by norm_num) psi_lower

end
end Wu2008DoubleSieve.HighSixPhase5
