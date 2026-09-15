import R2MatrixXi2
import R2MatrixFirstIdentity

noncomputable section
namespace WuPaper.R2Matrix
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval BigOperators Matrix

def secondSourceFeedback (p : SecondFunctionalParameters) (f : ℝ → ℝ) : ℝ :=
  aProfile f * (log (1024 / xi2Product p) / 5) +
    ∑ j : Fin 9, ∫ t in xi2Left p j..xi2Right p j, f t * xi2Weight p j t

theorem supported_weight_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (f w : ℝ → ℝ) :
    (∫ t in (1 : ℝ)..3, f t * (Icc a b).indicator (fun _ => (1 : ℝ)) t * w t) =
      ∫ t in a..b, f t * w t := by
  have he (t : ℝ) :
      f t * (Icc a b).indicator (fun _ => (1 : ℝ)) t * w t =
      (Icc a b).indicator (fun t => f t * w t) t := by
    by_cases ht : t ∈ Icc a b <;> simp [ht]
  simp_rw [he]
  exact WuPaper.RMapMSigma.indicator_interval_integral ha hab hb _

theorem secondSourceFeedback_eq_original_integral (i : Fin 4) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    secondSourceFeedback (coupledRow i) f =
      ∫ t in (1 : ℝ)..3, f t * xi2 t (coupledRow i) := by
  let p := coupledRow i
  have h1 := (WuPaper.RMapMSigma.sigma_weight_integrable hf).mul_const
    (log (1024 / xi2Product p) / 5)
  have hj (j : Fin 9) := supported_weight_integrable hf (xi2_support_geometry i j).1
    (xi2_support_geometry i j).2.1 (xi2_support_geometry i j).2.2
    (xi2_weight_continuous i j)
  have hsum : IntervalIntegrable (fun t => ∑ j : Fin 9,
      f t * (Icc (xi2Left p j) (xi2Right p j)).indicator (fun _ => (1 : ℝ)) t *
        xi2Weight p j t) volume 1 3 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mpr
    apply integrable_finsetSum
    intro j _
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (1 : ℝ) ≤ 3)).mp (hj j)
  have he (t : ℝ) :
      f t * xi2 t p =
      f t * sigma0 t / t * (log (1024 / xi2Product p) / 5) +
        ∑ j : Fin 9, f t *
          (Icc (xi2Left p j) (xi2Right p j)).indicator (fun _ => (1 : ℝ)) t *
          xi2Weight p j t := by
    unfold xi2
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  change secondSourceFeedback p f = ∫ t in (1 : ℝ)..3, f t * xi2 t p
  simp_rw [he]
  rw [intervalIntegral.integral_add h1 hsum,
    intervalIntegral.integral_finsetSum (fun j _ => hj j),
    intervalIntegral.integral_mul_const]
  unfold secondSourceFeedback aProfile
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (supported_weight_integral (xi2_support_geometry i j).1
    (xi2_support_geometry i j).2.1 (xi2_support_geometry i j).2.2 f _).symm

def sourceFeedback (z : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  if h : i.val < 4 then
    secondSourceFeedback (coupledRow ⟨i.val, h⟩) (nineProfile z)
  else firstFeedback z (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩)

def sourceKernel (i : Fin 9) (t : ℝ) : ℝ :=
  if h : i.val < 4 then xi2 t (coupledRow ⟨i.val, h⟩)
  else Wu04Source.xi1 t (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩)

def sourceMatrix : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i k => sourceFeedback (nodeBasis k) i

theorem sourceKernel_weighted_integrable (i : Fin 9) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun t => f t * sourceKernel i t) volume 1 3 := by
  unfold sourceKernel
  split_ifs
  · exact xi2_weighted_integrable _ hf
  · exact xi1_weighted_integrable _ hf

theorem sourceKernel_integrable (i : Fin 9) :
    IntervalIntegrable (sourceKernel i) volume 1 3 := by
  simpa only [one_mul] using sourceKernel_weighted_integrable i
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 3)

theorem sourceKernel_nonnegative (i : Fin 9) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    0 ≤ sourceKernel i t := by
  unfold sourceKernel
  split_ifs
  · exact xi2_nonnegative _ ht
  · exact xi1_nonnegative _ ht

theorem sourceFeedback_eq_original_integral (z : Fin 9 → ℝ) (i : Fin 9) :
    sourceFeedback z i = ∫ t in (1 : ℝ)..3, nineProfile z t * sourceKernel i t := by
  unfold sourceFeedback sourceKernel
  split_ifs
  · exact secondSourceFeedback_eq_original_integral _ (nineProfile_integrable z)
  · exact firstFeedback_eq_original_integral _ z

theorem original_matrix_entries (i k : Fin 9) :
    sourceMatrix i k =
      ∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
        sourceKernel i t := by
  rw [sourceMatrix, sourceFeedback_eq_original_integral]
  exact original_basis_coefficient k (sourceKernel_integrable i)

theorem original_second_matrix_entries (i : Fin 4) (k : Fin 9) :
    sourceMatrix ⟨i.val, by omega⟩ k =
      ∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
        xi2 t (coupledRow i) := by
  rw [original_matrix_entries]
  congr 1
  funext t
  simp [sourceKernel, i.isLt]

theorem original_first_matrix_entries (i : Fin 5) (k : Fin 9) :
    sourceMatrix ⟨i.val + 4, by omega⟩ k = feedbackMatrix ⟨i.val + 4, by omega⟩ k := by
  simp [sourceMatrix, sourceFeedback, feedbackMatrix, feedback]

theorem source_terminal_row (k : Fin 9) : sourceMatrix 8 k = Wu04Source.a9 k := by
  have h := original_first_matrix_entries (4 : Fin 5) k
  change sourceMatrix 8 k = feedbackMatrix 8 k at h
  exact h.trans (Wu04Source.coefficient_eq_project k)

theorem original_matrix_nonnegative (i k : Fin 9) : 0 ≤ sourceMatrix i k := by
  rw [original_matrix_entries]
  have hb := source_cell_bounds k
  apply intervalIntegral.integral_nonneg hb.2.1
  intro t ht
  exact sourceKernel_nonnegative i ⟨hb.1.trans ht.1, ht.2.trans hb.2.2⟩

theorem sourceFeedback_expansion (z : Fin 9 → ℝ) (i : Fin 9) :
    sourceFeedback z i = ∑ k : Fin 9, sourceMatrix i k * z k := by
  rw [sourceFeedback_eq_original_integral, original_cell_decomposition _ (sourceKernel_integrable i)]
  apply Finset.sum_congr rfl
  intro k _
  rw [original_matrix_entries, mul_comm]

theorem original_H_discretization {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 9) :
    (∑ k : Fin 9, sourceMatrix i k * actualNine δ k) ≤
      ∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * sourceKernel i t := by
  simp_rw [original_matrix_entries]
  exact original_monotone_discretization hd hh (sourceKernel_integrable i)
    (sourceKernel_weighted_integrable i (wuImprovementLimit_intervalIntegrable true hd
      (by linarith : δ < 1 / 2) (by norm_num) (by norm_num) (by norm_num)))
    (fun _ ht => sourceKernel_nonnegative i ht)

theorem source_same_forcing_discretization (B : Fin 9 → ℝ) {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 9) :
    B i + (∑ k : Fin 9, sourceMatrix i k * actualNine δ k) ≤
      B i + ∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * sourceKernel i t :=
  add_le_add le_rfl (original_H_discretization hd hh i)

theorem source_matrix_residual (z : Fin 9 → ℝ) (i : Fin 9) :
    ((1 - sourceMatrix) *ᵥ z) i = z i - ∑ k : Fin 9, sourceMatrix i k * z k := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

theorem original_residual_dominates_functional_residual {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 9) :
    actualNine δ i -
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * sourceKernel i t) ≤
      ((1 - sourceMatrix) *ᵥ actualNine δ) i := by
  rw [source_matrix_residual]
  exact sub_le_sub_left (original_H_discretization hd hh i) _

theorem first_original_actual_rows (i : Fin 5) {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    firstFunctionalGainPsiOne (firstNode i) (firstS i) -
      deltaLoss δ * omega3XIntegralEnvelope (firstNode i) (firstS i) +
      (∑ k : Fin 9, sourceMatrix ⟨i.val + 4, by omega⟩ k * actualNine δ k) ≤
      wuImprovementLimit true δ (firstNode i) := by
  have hg := first_geometry i
  have h := first_actual hd hh hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  rw [firstFeedback_expansion _ hg.1 hg.2.2.1 hg.2.2.2.1
    (hg.2.1.trans hg.2.2.1) hg.2.2.2.2] at h
  convert h using 2

end WuPaper.R2Matrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
