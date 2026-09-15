import Wu04RemainingCore

namespace Wu04RemainingLower
open Wu2008DoubleSieve Set MeasureTheory Wu04RemainingCore Wu04MainTail
open SecondFunctionalParameters SecondFunctionalGeometricMass SecondFunctionalJointTail
open SecondFunctionalFourSevenths
open scoped BigOperators
noncomputable section

/-- Gate verified at each ORIGINAL band, not inherited from first-row geometry. -/
theorem original_gate (i : Fin 3) (j : Fin 6) {t : Fin 3 → ℝ}
    (ht : t∈LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j) :
    t 0+(1+1/cap)*t 1+t 2≤2 := by
  have all : ∀ i : Fin 3, ∀ j : Fin 6,
      t∈LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
        (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j →
      t 0+(1+1/cap)*t 1+t 2≤2 := by
    simp only [row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
      Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,
      LowerTripleContinuous.D,LowerTripleGrouped.bands,Matrix.cons_val_zero,Matrix.cons_val_succ]
    repeat' constructor
    all_goals rintro ⟨_,h0,_,h1,_,h2,_,_⟩
    all_goals norm_num only [row2,row3,row4,cap] at *
    all_goals linarith only [h0,h1,h2]
  exact all i j ht

/-- Whole-domain mass payment, with the selected coordinate squared. -/
theorem lower_paid (i : Fin 3) (j : Fin 6) {φ : ℝ} (hφ : 2≤φ) :
    LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1) (1/(row i).kappa2)
      (1/(row i).kappa3) (1/(row i).s) j φ≤cap*lowerMass (row i) j := by
  have hd := LowerTripleContinuous.D_subset_cube (original_compact i.succ) j
  have hi := LowerTripleContinuous.K_integrable (original_compact i.succ) j φ
  have hw := geometricWeight_integrable 1 hd
  change (∫ t in _, LowerTripleContinuous.G φ t*continuousDensity t)≤
    cap*(∫ t in _,geometricWeight 1 t)
  rw [← integral_const_mul]
  refine setIntegral_mono_on hi (hw.const_mul cap) (LowerTripleContinuous.D_measurable _ _ _ _ _ j) ?_
  intro t ht
  have ht' := hd ht
  have hpos : 0<t 1 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/10) (ht' 1 (mem_univ 1)).1
  have gate := original_gate i j ht
  have harg : 1/cap≤(φ-(t 0+t 1+t 2))/t 1 := by
    apply (le_div_iff₀ hpos).mpr
    linarith only [gate,hφ]
  have hcap : 0<cap := by norm_num [cap]
  have hu : 1≤cap*((φ-(t 0+t 1+t 2))/t 1) := by
    have hm := mul_le_mul_of_nonneg_left harg hcap.le
    rwa [mul_one_div_cancel hcap.ne'] at hm
  have hω := buchstab_le hu
  rw [LowerTripleContinuous.G_cube_literal hφ ht']
  have hpoint := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hω hpos.le)
    (continuousDensity_nonneg ht')
  convert hpoint using 1
  simp only [geometricWeight]
  ring

theorem six_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    (∑ j : Fin 6, LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1)
      (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) j φ)≤
    cap*(∑ j : Fin 6,lowerMass (row i) j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => lower_paid i j hφ)

end
end Wu04RemainingLower
