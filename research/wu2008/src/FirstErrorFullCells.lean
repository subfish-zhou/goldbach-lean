import FirstErrorFullKernel

namespace FirstErrorFullPayment
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open Wu2008DoubleSieve SharpLogRecurrence Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

/-- Combine identical logarithms before signed endpoint payment. -/
def correctedCell (S a b : ℝ) : ℝ :=
  signedLow (ea S+2/(21*(S-1))*qa S) (b/a)+
  signedLow (2/(21*(S-1))*qb S) ((b+1)/(a+1))+
  signedLow (eb S+2/(21*(S-1))*qc S) ((b+S)/(a+S))+
  2/(21*(S-1))*(b-a)-
  (ec S+2/(21*(S-1))*qd S)*(1/(b+S)-1/(a+S))-
  (ed S+2/(21*(S-1))*qe S)/2*(1/(b+S)^2-1/(a+S)^2)

theorem correctedCell_le_primitive {S a b : ℝ} (hS : 3≤S) (ha : 0<a) (hab : a≤b) :
    correctedCell S a b ≤
      (ePrimitive S b+errorPrimitive S b)-(ePrimitive S a+errorPrimitive S a) := by
  have hb : 0<b := ha.trans_le hab
  have ha1 : 0<a+1 := by linarith
  have hb1 : 0<b+1 := by linarith
  have has : 0<a+S := by linarith
  have hbs : 0<b+S := by linarith
  have h0 := signed_bound (ea S+2/(21*(S-1))*qa S) (div_pos hb ha)
  have h1 := signed_bound (2/(21*(S-1))*qb S) (div_pos hb1 ha1)
  have h2 := signed_bound (eb S+2/(21*(S-1))*qc S) (div_pos hbs has)
  rw [log_div hb.ne' ha.ne'] at h0
  rw [log_div hb1.ne' ha1.ne'] at h1
  rw [log_div hbs.ne' has.ne'] at h2
  dsimp [correctedCell,ePrimitive,errorPrimitive]
  simp only [div_eq_mul_inv,mul_inv_rev] at h0 h1 h2 ⊢
  ring_nf at h0 h1 h2 ⊢
  linarith only [h0,h1,h2]

theorem corrected_integral {S a b : ℝ} (hS : 3≤S) (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,lowerLog ((t+1)/(S-1))/t+errorDensity S t)=
      (ePrimitive S b+errorPrimitive S b)-(ePrimitive S a+errorPrimitive S a) := by
  rw [intervalIntegral.integral_add (lower_e_integrable hS ha hab)
    (errorDensity_continuous hS ha hab).intervalIntegrable,error_integral hS ha hab]
  have he : (∫ t in a..b,lowerLog ((t+1)/(S-1))/t)=ePrimitive S b-ePrimitive S a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact ePrimitive_deriv hS (ha.trans_le ht.1)
    · exact lower_e_integrable hS ha hab
  rw [he]
  ring

theorem correctedCell_paid {S a b : ℝ} (hS : 3≤S) (ha : S-2≤a) (hab : a≤b) (hb : b≤3) :
    correctedCell S a b ≤ ∫ t in a..b,log ((t+1)/(S-1))/t := by
  have ha0 : 0<a := by linarith
  refine ((correctedCell_le_primitive hS ha0 hab).trans_eq
    (corrected_integral hS ha0 hab).symm).trans ?_
  apply intervalIntegral.integral_mono_on hab
    ((lower_e_integrable hS ha0 hab).add (errorDensity_continuous hS ha0 hab).intervalIntegrable)
  · apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht0 : 0<t := ha0.trans_le ht.1
    have hs0 : 0<S-1 := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  · intro t ht
    exact corrected_le hS (ha.trans ht.1) (ht.2.trans hb)

/-- No original profile cell is dropped; the first cell keeps its original clipping. -/
def correctedCells (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*correctedCell S (cellLeft (S-2) k) (upperNode k)

theorem correctedCells_paid {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {S : ℝ}
    (hS : 3≤S) (hS2 : S-2≤upperNode 0) :
    aProfile (nineProfile z)*log (4/(S-1))+correctedCells z S≤eProfile (nineProfile z) S := by
  have hS5 : S≤5 := by have h := (upperNode_bounds 0).2; linarith
  have hw : ContinuousOn (fun t => log ((t+1)/(S-1))/t) (uIcc (S-2) 3) := by
    apply ContinuousOn.div (log_weight_continuous hS hS5) continuousOn_id
    intro t ht
    rw [uIcc_of_le (by linarith : S-2≤3)] at ht
    dsimp
    linarith [ht.1]
  have he := profile_integral_cells z (by linarith : 1≤S-2) hS2 hw
  have hm : correctedCells z S ≤
      ∫ t in (S-2)..3,nineProfile z t*(log ((t+1)/(S-1))/t) := by
    rw [he]
    apply Finset.sum_le_sum
    intro k _
    have hb := cell_bounds (by linarith : 1≤S-2) hS2 k
    exact mul_le_mul_of_nonneg_left (correctedCell_paid hS hb.1 hb.2.1 hb.2.2.1) (hz k)
  unfold eProfile
  apply add_le_add le_rfl
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using hm

/-- Exact replacement in the old eCells interface, not an extra copy of E. -/
def eRecovery (z : Fin 9 → ℝ) (S : ℝ) : ℝ := correctedCells z S-eCells z S

theorem original_eCells_recovered {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {S : ℝ}
    (hS : 3≤S) (hS2 : S-2≤upperNode 0) :
    aProfile (nineProfile z)*log (4/(S-1))+eCells z S+eRecovery z S≤eProfile (nineProfile z) S := by
  have h := correctedCells_paid hz hS hS2
  unfold eRecovery
  linarith only [h]

end
end FirstErrorFullPayment
