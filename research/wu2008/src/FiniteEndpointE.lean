import FiniteEndpointCells

namespace FiniteEndpointPayment
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open FirstFeedbackIntegrals
open scoped Interval BigOperators
noncomputable section

/-- Exact log tail on all original cells, not just the first cell. -/
def tail (z : Fin 9 → ℝ) (a : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*log (right a 3 k/left a 3 k)

theorem tail_eq (z : Fin 9 → ℝ) {a : ℝ} (ha : 1≤a) (ha3 : a≤3) :
    (∫ t in a..3,nineProfile z t/t)=tail z a := by
  have hi := profile_subinterval (profile_div_integrable (nineProfile_integrable z)) ha ha3
  have he := integral_cells z (w := fun t => 1/t) ha ha3 le_rfl (by simpa only [mul_one_div] using hi)
  simp only [mul_one_div] at he
  rw [he]
  unfold tail
  apply Finset.sum_congr rfl
  intro k _
  rw [inv_integral (by have h := (clip_bounds (x := upperLeft k) ha3).1; change 0<clip a 3 (upperLeft k); linarith)
    (cell_order a 3 k)]

theorem g_tail_eq (z : Fin 9 → ℝ) {S : ℝ} (hS : 3≤S) (hS5 : S≤5) :
    gProfile (nineProfile z) (S-1)=aProfile (nineProfile z)+tail z (S-2) := by
  unfold gProfile
  rw [show S-1-1=S-2 by ring,tail_eq z (by linarith) (by linarith)]

/-- The two original E terms admit this complete finite endpoint lower payment. -/
def e (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  aProfile (nineProfile z)*log (4/(S-1))+
    ∑ k : Fin 9,z k*eCell S (left (S-2) 3 k) (right (S-2) 3 k)

theorem e_le (z : Fin 9 → ℝ) (hz : ∀ k,0≤z k) {S : ℝ}
    (hS : 3≤S) (hS5 : S≤5) : e z S≤eProfile (nineProfile z) S := by
  have hab : S-2≤3 := by linarith
  have ha : 1≤S-2 := by linarith
  have hw : ContinuousOn (fun t => log ((t+1)/(S-1))/t) (uIcc (S-2) 3) := by
    apply ContinuousOn.div (log_weight_continuous hS hS5) continuousOn_id
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp
    linarith [ht.1]
  have hi := (profile_subinterval (nineProfile_integrable z) ha hab).mul_continuousOn hw
  have he := integral_cells z ha hab le_rfl hi
  unfold e eProfile
  apply add_le_add le_rfl
  calc
    _ ≤ ∫ t in (S-2)..3,nineProfile z t*(log ((t+1)/(S-1))/t) := by
      rw [he]
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (eCell_paid hS (clip_bounds hab).1 (cell_order _ _ k)) (hz k)
    _ = _ := by congr 1; funext t; ring

end
end FiniteEndpointPayment
