import NinePositivity

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

theorem matrixApply_scale (r : ℝ) (z : Fin 9 → ℝ) (i : Fin 9) :
    matrixApply feedbackMatrix (fun k => r*z k) i = r*matrixApply feedbackMatrix z i := by
  simp only [matrixApply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Genuine positive forcing propagates through the retained terminal feedback. -/
theorem supersolution_pos {b z : Fin 9 → ℝ}
    (hb : ∀ i,0≤b i) (hbp : ∀ i : Fin 9,i≠8 → 0<b i)
    (hz : ∀ i,0≤z i) (hs : ∀ i,b i+matrixApply feedbackMatrix z i≤z i) :
    ∀ i,0<z i := by
  have hn i := matrixApply_nonneg feedbackMatrix_nonneg hz i
  have h0 : 0<z 0 := (lt_add_of_pos_of_le (hbp 0 (by decide)) (hn 0)).trans_le (hs 0)
  intro i
  by_cases hi : i=8
  · subst i
    have hterm : feedbackMatrix 8 0*z 0 ≤ matrixApply feedbackMatrix z 8 :=
      Finset.single_le_sum (fun k _ => mul_nonneg (feedbackMatrix_nonneg 8 k) (hz k))
        (Finset.mem_univ 0)
    exact (mul_pos terminal_first_entry_pos h0).trans_le
      (hterm.trans ((le_add_of_nonneg_left (hb 8)).trans (hs 8)))
  · exact (lt_add_of_pos_of_le (hbp i hi) (hn i)).trans_le (hs i)

/-- A maximum-ratio comparison for the ACTUAL matrix. The exceptional zero-base terminal
cannot trap a positive discrepancy because its first-column entry is strictly positive.
No least-fixed-point direction is reversed; no norm bound or guessed matrix is assumed. -/
theorem subsolution_le_supersolution {b x z : Fin 9 → ℝ}
    (hb : ∀ i,0≤b i) (hbp : ∀ i : Fin 9,i≠8 → 0<b i)
    (hz : ∀ i,0≤z i)
    (hx : ∀ i,x i≤b i+matrixApply feedbackMatrix x i)
    (hs : ∀ i,b i+matrixApply feedbackMatrix z i≤z i) : ∀ i,x i≤z i := by
  classical
  have hp := supersolution_pos hb hbp hz hs
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 9 => x i/z i) Finset.univ_nonempty
  let r : ℝ := x j/z j
  have hall : ∀ i,x i≤r*z i := by
    intro i
    exact (div_le_iff₀ (hp i)).mp (hj i (Finset.mem_univ i))
  have he : x j=r*z j := (div_mul_cancel₀ (x j) (ne_of_gt (hp j))).symm
  have hr : r≤1 := by
    by_contra h
    have hr1 : 1<r := lt_of_not_ge h
    have hr0 : 0≤r := by linarith only [hr1]
    have hm (i : Fin 9) : matrixApply feedbackMatrix x i≤r*matrixApply feedbackMatrix z i := by
      rw [← matrixApply_scale]
      exact matrixApply_mono feedbackMatrix_nonneg hall i
    have hstrict (i : Fin 9) (hi : i≠8) : x i<r*z i := by
      have hbi := hbp i hi
      have hprod := mul_pos (sub_pos.mpr hr1) hbi
      have hscaled := mul_le_mul_of_nonneg_left (hs i) hr0
      nlinarith only [hx i,hm i,hscaled,hprod]
    by_cases hj8 : j=8
    · have hm8 : matrixApply feedbackMatrix x 8<r*matrixApply feedbackMatrix z 8 := by
        rw [← matrixApply_scale]
        apply Finset.sum_lt_sum
        · intro k _
          exact mul_le_mul_of_nonneg_left (hall k) (feedbackMatrix_nonneg 8 k)
        · exact ⟨0,Finset.mem_univ 0,mul_lt_mul_of_pos_left (hstrict 0 (by decide)) terminal_first_entry_pos⟩
      have hscaled := mul_le_mul_of_nonneg_left (hs 8) hr0
      have hprod := mul_nonneg (sub_nonneg.mpr hr1.le) (hb 8)
      rw [hj8] at he
      nlinarith only [hx 8,hm8,hscaled,hprod,he]
    · exact (hstrict j hj8).ne he
  intro i
  exact (hall i).trans (by nlinarith only [hr,hz i])

/-- The missing lower comparison is now proved for the original Ainf, without extra analytic premises. -/
theorem subsolution_le_Ainf {x : Fin 9 → ℝ}
    (hx : ∀ i,x i≤base i+matrixApply feedbackMatrix x i) : ∀ i,x i≤FeedbackLimit.Ainf i :=
  subsolution_le_supersolution base_nonneg (fun _ h => base_pos h) FeedbackLimit.Ainf_nonneg hx
    FeedbackLimit.Ainf_supersolution

/-- Uniqueness concerns the genuine affine system, not the printed matrix. -/
theorem affine_fixed_unique {z : Fin 9 → ℝ} (hz : ∀ i,0≤z i)
    (hs : ∀ i,z i=base i+matrixApply feedbackMatrix z i) : z=FeedbackLimit.Ainf := by
  funext i
  exact le_antisymm (subsolution_le_Ainf (fun j => (hs j).le) i)
    (FeedbackLimit.Ainf_le_supersolution hz (fun j => (hs j).ge) i)

/-- Every genuine publication subsolution bounds the same actual delta on all nine rows. -/
theorem actual_comparison_same_delta : ∃ d : ℝ,0<d ∧ d≤1/10 ∧
    ∀ δ : ℝ,0<δ → δ≤d → ∀ x : Fin 9 → ℝ,
      (∀ i,x i≤publication i+matrixApply feedbackMatrix x i) → ∀ i,x i≤actualNine δ i := by
  obtain ⟨d,hd,hcap,hs⟩ := actual_same_delta
  refine ⟨d,hd,hcap,?_⟩
  intro δ hδ hr x hx
  exact subsolution_le_supersolution publication_nonneg (fun _ h => publication_pos h)
    (actualNine_nonneg hδ (hr.trans hcap)) hx (hs δ hδ hr)

end
end NineFeedbackStrength
