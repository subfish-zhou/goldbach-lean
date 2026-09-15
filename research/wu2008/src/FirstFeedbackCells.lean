import FirstFeedbackKernel

namespace FirstFeedbackIntegrals
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open scoped Interval BigOperators
noncomputable section

def cellLeft (a : ℝ) (k : Fin 9) : ℝ := if k.val=0 then a else upperLeft k

theorem cell_bounds {a : ℝ} (ha : 1≤a) (ha2 : a≤upperNode 0) (k : Fin 9) :
    a≤cellLeft a k ∧ cellLeft a k≤upperNode k ∧ upperNode k≤3 ∧
      upperLeft k≤cellLeft a k := by
  have hk0 : (0:ℝ)≤k.val := Nat.cast_nonneg _
  have hk8 : (k.val:ℝ)≤8 := by exact_mod_cast (show k.val≤8 by omega)
  by_cases hk : k.val=0
  · have hke : k=(0:Fin 9) := Fin.ext hk
    subst k
    norm_num [cellLeft,upperLeft,upperNode] at ha2 ⊢
    exact ⟨ha2,ha⟩
  · have hk1 : (1:ℝ)≤k.val := by exact_mod_cast (show 1≤k.val by omega)
    simp only [cellLeft,upperLeft,if_neg hk,upperNode] at *
    norm_num at ha2
    constructor
    · linarith
    constructor
    · linarith
    exact ⟨by linarith,le_rfl⟩

theorem profile_cell_integral (z : Fin 9 → ℝ) (w : ℝ → ℝ) {a : ℝ}
    (ha : 1≤a) (ha2 : a≤upperNode 0) (k : Fin 9) :
    (∫ t in cellLeft a k..upperNode k, nineProfile z t*w t)=
      z k*(∫ t in cellLeft a k..upperNode k,w t) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  rw [uIoo_of_le (cell_bounds ha ha2 k).2.1] at ht
  dsimp only
  rw [nineProfile_cell z (i := k)
    ⟨lt_of_le_of_lt (cell_bounds ha ha2 k).2.2.2 ht.1,ht.2.le⟩]

theorem profile_integral_cells (z : Fin 9 → ℝ) {w : ℝ → ℝ} {a : ℝ}
    (ha : 1≤a) (ha2 : a≤upperNode 0) (hw : ContinuousOn w (uIcc a 3)) :
    (∫ t in a..3,nineProfile z t*w t)=
      ∑ k : Fin 9,z k*(∫ t in cellLeft a k..upperNode k,w t) := by
  have ha3 : a≤3 := ha2.trans (upperNode_bounds 0).2
  have hi := (profile_subinterval (nineProfile_integrable z) ha ha3).mul_continuousOn hw
  let x : ℕ → ℝ := fun n => if n=0 then a else (21+(n:ℝ))/10
  have hx (k : Fin 9) : x k.val=cellLeft a k ∧ x (k.val+1)=upperNode k := by
    constructor
    · simp only [x,cellLeft,upperLeft]
      split_ifs <;> rfl
    · simp [x,upperNode,Nat.cast_add]
      ring
  have hic (k : ℕ) (hk : k<9) :
      IntervalIntegrable (fun t => nineProfile z t*w t) volume (x k) (x (k+1)) := by
    have h := cell_bounds ha ha2 (⟨k,hk⟩ : Fin 9)
    rw [(hx ⟨k,hk⟩).1,(hx ⟨k,hk⟩).2]
    apply hi.mono_set
    rw [uIcc_of_le h.2.1,uIcc_of_le ha3]
    exact Icc_subset_Icc h.1 h.2.2.1
  have ht := intervalIntegral.sum_integral_adjacent_intervals hic
  have hsum : (∑ k : Fin 9,∫ t in x k.val..x (k.val+1),nineProfile z t*w t)=
      ∫ t in a..3,nineProfile z t*w t := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in x k..x (k+1),nineProfile z t*w t) 9]
    norm_num [x] at ht ⊢
    exact ht
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hx k).1,(hx k).2]
  exact profile_cell_integral z w ha ha2 k

/-- Every original profile cell is retained, including the clipped first cell. -/
def eCells (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*eCell S (cellLeft (S-2) k) (upperNode k)

theorem eCells_paid {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {S : ℝ}
    (hS : 3≤S) (hS2 : S-2≤upperNode 0) :
    aProfile (nineProfile z)*log (4/(S-1))+eCells z S≤eProfile (nineProfile z) S := by
  have hS5 : S≤5 := by have h := (upperNode_bounds 0).2; linarith
  have hw : ContinuousOn (fun t => log ((t+1)/(S-1))/t) (uIcc (S-2) 3) := by
    apply ContinuousOn.div
    · exact log_weight_continuous hS hS5
    · exact continuousOn_id
    · intro t ht
      rw [uIcc_of_le (by linarith : S-2≤3)] at ht
      dsimp
      linarith [ht.1]
  have he := profile_integral_cells z (by linarith : 1≤S-2) hS2 hw
  have hm : eCells z S≤∫ t in (S-2)..3,nineProfile z t*(log ((t+1)/(S-1))/t) := by
    rw [he]
    apply Finset.sum_le_sum
    intro k _
    have hb := cell_bounds (by linarith : 1≤S-2) hS2 k
    exact mul_le_mul_of_nonneg_left (eCell_paid hS hb.1 hb.2.1) (hz k)
  unfold eProfile
  apply add_le_add le_rfl
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using hm

end
end FirstFeedbackIntegrals
