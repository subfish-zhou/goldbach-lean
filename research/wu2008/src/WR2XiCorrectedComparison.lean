import WR2XiCorrectedMatrix

/-! Monotone comparison for the exact corrected second-functional integral. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory Wu2008DoubleSieve MotherPair
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval

private theorem loss_integrable (r : Fin 4) {f : ℝ → ℝ}
    (hm : Measurable f) (hb : ∀ t, 0 ≤ f t ∧ f t ≤ 1) :
    IntervalIntegrable (fun t => f t *
      generalKernel (rowParameters r).1 (rowParameters r).2 t) volume 1 3 := by
  have hp : 0 < (rowParameters r).1 ∧ 1/3 ≤ (rowParameters r).2 ∧
      (rowParameters r).2 < 1/2 ∧
      5/4 ≤ (rowParameters r).1*(1-2*(rowParameters r).2) := by
    fin_cases r <;> norm_num [rowParameters]
  exact (general_weighted_integrable hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 f hm
    (fun t _ => hb t)).intervalIntegrable

/-- Increasing the input increases the corrected integral, despite its subtraction formula. -/
theorem Xi2_corrected_integral_mono (r : Fin 4) {f g : ℝ → ℝ}
    (hfi : IntervalIntegrable f volume 1 3) (hgi : IntervalIntegrable g volume 1 3)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (hgb : ∀ t, 0 ≤ g t ∧ g t ≤ 1)
    (hfg : ∀ t ∈ Icc (1:ℝ) 3, f t ≤ g t) :
    (∫ t in (1:ℝ)..3, f t * Xi2 (gamma5OriginalRow r) t) -
      (∫ t in (1:ℝ)..3, f t * generalKernel (rowParameters r).1 (rowParameters r).2 t) ≤
    (∫ t in (1:ℝ)..3, g t * Xi2 (gamma5OriginalRow r) t) -
      (∫ t in (1:ℝ)..3, g t * generalKernel (rowParameters r).1 (rowParameters r).2 t) := by
  have hb (t : ℝ) : |g t - f t| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hfb t).1,(hfb t).2,(hgb t).1,(hgb t).2]
  have h := Xi2_corrected_integral_nonneg r (hgi.sub hfi) (hgm.sub hfm) hb
    (fun t ht => sub_nonneg.mpr (hfg t ht))
  have hp : WuPaper.RMapMMatrix.PropositionFourGeometry (gamma5OriginalRow r) :=
    WuPaper.RMapMMatrix.original_four_rows_qualified r
  simp only [sub_mul] at h
  rw [intervalIntegral.integral_sub (Xi2_integrable hgi hp) (Xi2_integrable hfi hp),
    intervalIntegral.integral_sub (loss_integrable r hgm hgb) (loss_integrable r hfm hfb)] at h
  linarith only [h]

end WuPaper.R2Xi
