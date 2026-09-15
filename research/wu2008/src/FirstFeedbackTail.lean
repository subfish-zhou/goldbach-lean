import FirstFeedbackCells

namespace FirstFeedbackIntegrals
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open Wu04WholeCollection SharpLogRecurrence
open scoped Interval BigOperators
noncomputable section

theorem inv_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,(1:ℝ)/t)=log (b/a) := by
  rw [log_div (ha.trans_le hab).ne' ha.ne']
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    simpa only [one_div] using hasDerivAt_log (ha.trans_le ht.1).ne'
  · exact (reciprocal_continuous ha hab).intervalIntegrable

def tailCells (z : Fin 9 → ℝ) (a : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*low (upperNode k/cellLeft a k)

theorem low_nonneg {x : ℝ} (hx : 1≤x) : 0≤low x := by
  rw [low,if_pos hx]
  unfold Wu04FactorEnvelopes.lower lowerLog
  have h1 := (Wu04FactorEnvelopes.factors hx).1
  have h2 := (Wu04FactorEnvelopes.factors hx).2.1
  positivity

theorem tailCells_nonneg {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {a : ℝ}
    (ha : 1≤a) (ha2 : a≤upperNode 0) : 0≤tailCells z a := by
  apply Finset.sum_nonneg
  intro k _
  have h := cell_bounds ha ha2 k
  exact mul_nonneg (hz k) (low_nonneg ((one_le_div (by linarith : 0<cellLeft a k)).mpr h.2.1))

theorem tailCells_paid {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {a : ℝ}
    (ha : 1≤a) (ha2 : a≤upperNode 0) :
    tailCells z a≤∫ t in a..3,nineProfile z t/t := by
  have ha3 := ha2.trans (upperNode_bounds 0).2
  have he := profile_integral_cells z ha ha2 (reciprocal_continuous (by linarith : 0<a) ha3)
  simp only [mul_one_div] at he
  rw [he]
  apply Finset.sum_le_sum
  intro k _
  have h := cell_bounds ha ha2 k
  rw [inv_integral (by linarith : 0<cellLeft a k) h.2.1]
  exact mul_le_mul_of_nonneg_left
    (bounds (div_pos (by linarith : 0<upperNode k) (by linarith : 0<cellLeft a k))).1 (hz k)

theorem first_cell_tail (z : Fin 9 → ℝ) {a b : ℝ}
    (ha : 1≤a) (hab : a≤b) (hb : b≤upperNode 0) :
    (∫ t in a..b,nineProfile z t/t)=z 0*log (b/a) := by
  rw [← inv_integral (by linarith : 0<a) hab,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  dsimp only
  rw [nineProfile_cell z (i := 0) ⟨by change (1:ℝ)<t; linarith [ht.1],ht.2.le.trans hb⟩]
  ring

/-- Exact lower-tail identity on the original first cell; no monotonicity loss. -/
theorem g_first_cell (z : Fin 9 → ℝ) {S u : ℝ}
    (hl : 2≤S*u) (hu : S*u≤S-1) (hS2 : S-2≤upperNode 0) :
    gProfile (nineProfile z) (S*u)=
      aProfile (nineProfile z)+(∫ t in (S-2)..3,nineProfile z t/t)+
        z 0*log ((S-2)/(S*u-1)) := by
  have ha : 1≤S*u-1 := by linarith
  have hab : S*u-1≤S-2 := by linarith
  have hb3 : S-2≤3 := hS2.trans (upperNode_bounds 0).2
  have hi := profile_div_integrable (nineProfile_integrable z)
  have hiab : IntervalIntegrable (fun t => nineProfile z t/t) volume (S*u-1) (S-2) := by
    apply hi.mono_set
    rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (1:ℝ)≤3)]
    exact Icc_subset_Icc ha hb3
  have hib3 := profile_subinterval hi (ha.trans hab) hb3
  have he := intervalIntegral.integral_add_adjacent_intervals hiab hib3
  rw [first_cell_tail z ha hab hS2] at he
  unfold gProfile
  linarith only [he]

end
end FirstFeedbackIntegrals
