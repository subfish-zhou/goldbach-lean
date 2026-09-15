import W07DensityMatrices
import Wu04BypassActual

noncomputable section
namespace WuTarget.W07
open NodeExtension ActualNineFeedback Wu2008DoubleSieve Wu04Bypass
open scoped BigOperators

theorem cells_add_density_le_coupled {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) (hc : p.kappa1 - 2 ≤ upperNode 0)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    cells z p.kappa1 / 5 + densityMoment p z / 5 ≤ coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have h0 := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2
    p.S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
  have h1 := cells_le_eProfile hz hp.2.1 hc
  have hj0 := profileJ_nonneg hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := profileJ_nonneg hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_nonneg hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  unfold coupledFeedback
  linarith only [h0, h1, hj0, hj2, hj3]

theorem elementary_add_density_le (i k : Fin 9) :
    elementaryMatrix i k + densityMatrix i k ≤ feedbackMatrix i k := by
  unfold elementaryMatrix densityMatrix feedbackMatrix feedback
  split_ifs with h
  · rw [densityEntry_eq_basis _ (coupledRow_geometry _).1]
    simpa only [cells_basis] using cells_add_density_le_coupled
      (coupledRow_geometry ⟨i.val, h⟩) (coupled_kappa_cell ⟨i.val, h⟩) (nodeBasis_nonneg k)
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hg := first_geometry j
    simpa only [cells_basis, add_zero] using
      cells_le_first (nodeBasis_nonneg k) hg.1 hg.2.2.1 hg.2.2.2.1
        (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 (first_cell j)

theorem elementary_add_log_le (i k : Fin 9) :
    elementaryMatrix i k + logMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add le_rfl (logMatrix_le_densityMatrix i k)).trans (elementary_add_density_le i k)

theorem elementary_add_paid_le (i k : Fin 9) :
    elementaryMatrix i k + paidMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add le_rfl (paidMatrix_le_densityMatrix i k)).trans (elementary_add_density_le i k)

theorem baseline_le_elementary (i k : Fin 9) : M i k ≤ elementaryMatrix i k := by
  fin_cases i
  · exact matrix_row0 k
  · exact matrix_row1 k
  · exact matrix_row2 k
  · exact matrix_row3 k
  · exact matrix_row4 k
  · exact matrix_row5 k
  · exact matrix_row6 k
  · exact matrix_row7 k
  · exact matrix_row8 k

theorem baseline_add_paid_le (i k : Fin 9) :
    M i k + paidMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add (baseline_le_elementary i k) le_rfl).trans (elementary_add_paid_le i k)

theorem baseline_add_log_le (i k : Fin 9) :
    M i k + logMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add (baseline_le_elementary i k) le_rfl).trans (elementary_add_log_le i k)

theorem paid_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) (hza : ∀ k, z k ≤ actualNine δ k)
    (i : Fin 9) :
    base i - deltaLoss δ * loss i +
      (∑ k : Fin 9, (M i k + paidMatrix i k) * z k) ≤ actualNine δ i := by
  have hpaid := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_right (baseline_add_paid_le i k) (hz k))
  have hmono := matrixApply_mono feedbackMatrix_nonneg hza i
  have hsrc := actual_feedback hd hh i
  rw [feedback_expansion] at hsrc
  exact (add_le_add le_rfl (hpaid.trans hmono)).trans hsrc

theorem paid_v8_actual :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
        base i - deltaLoss δ * loss i +
          (∑ k : Fin 9, (M i k + paidMatrix i k) * v8 k) ≤ actualNine δ i := by
  obtain ⟨d, hd, hcap, hv⟩ := new_nine_actual
  exact ⟨d, hd, hcap, fun δ hδ hsmall i =>
    paid_actual hδ (hsmall.trans hcap) v8 v8_nonneg (hv δ hδ hsmall) i⟩

theorem coupled_paid_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 4) :
    coupledBase (coupledRow i) - deltaLoss δ * coupledLoss (coupledRow i) +
      (retainedCoupled (coupledRow i) (actualNine δ) +
        ∑ k : Fin 9, paidTable i k * actualNine δ k) ≤
      wuImprovementLimit true δ (coupledRow i).s :=
  (add_le_add le_rfl (coupled_paid_le i _ (actualNine_nonneg hd hh))).trans
    (coupled_actual (coupledRow_geometry i) hd hh)

end WuTarget.W07
