import R2MatrixProbe
import WRMapMMatrixGeometry
import Wu04SourceMatrix

noncomputable section
namespace WuPaper.R2Matrix
open Real Set MeasureTheory NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open Wu2008DoubleSieve
open scoped Interval BigOperators

theorem source_node_index_eq (i : Fin 9) :
    Wu04Source.paperNode (i.val + 1) = WuPaper.RMapMMatrix.wu08Node (i.val + 2) ∧
      Wu04Source.paperNode (i.val + 1) = upperNode i := by
  exact WuPaper.RMapMMatrix.source_node_index_eq i

theorem source_cell_bounds (k : Fin 9) :
    1 ≤ Wu04Source.paperNode k.val ∧
    Wu04Source.paperNode k.val ≤ Wu04Source.paperNode (k.val + 1) ∧
    Wu04Source.paperNode (k.val + 1) ≤ 3 := by
  rw [Wu04Source.node_left, Wu04Source.node_right]
  exact SigmaEndpointPayment.original_cell_bounds k

theorem profile_mul_integrable (z : Fin 9 → ℝ) {K : ℝ → ℝ}
    (hK : IntervalIntegrable K volume 1 3) :
    IntervalIntegrable (fun t => nineProfile z t * K t) volume 1 3 := by
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (1 : ℝ) ≤ 3)).mp hK
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (1 : ℝ) ≤ 3)).mpr
  have he : (fun t => nineProfile z t * K t) =
      fun t => ∑ k : Fin 9, (Ioc (upperLeft k) (upperNode k)).indicator
        (fun t => z k * K t) t := by
    funext t
    unfold nineProfile
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases ht : t ∈ Ioc (upperLeft k) (upperNode k) <;> simp [ht]
  rw [he]
  exact integrable_finsetSum _ (fun k _ =>
    (hI.const_mul (z k)).indicator measurableSet_Ioc)

theorem original_cell_decomposition (z : Fin 9 → ℝ) {K : ℝ → ℝ}
    (hK : IntervalIntegrable K volume 1 3) :
    (∫ t in (1 : ℝ)..3, nineProfile z t * K t) =
      ∑ k : Fin 9, z k *
        (∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1), K t) := by
  have hi := profile_mul_integrable z hK
  have hic (k : ℕ) (hk : k < 9) :
      IntervalIntegrable (fun t => nineProfile z t * K t) volume
        (Wu04Source.paperNode k) (Wu04Source.paperNode (k + 1)) := by
    have hb := source_cell_bounds (⟨k, hk⟩ : Fin 9)
    apply hi.mono_set
    rw [uIcc_of_le hb.2.1, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Icc_subset_Icc hb.1 hb.2.2
  have ht := intervalIntegral.sum_integral_adjacent_intervals hic
  have hsum :
      (∑ k : Fin 9, ∫ t in Wu04Source.paperNode k.val..
        Wu04Source.paperNode (k.val + 1), nineProfile z t * K t) =
      ∫ t in (1 : ℝ)..3, nineProfile z t * K t := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in Wu04Source.paperNode k..
      Wu04Source.paperNode (k + 1), nineProfile z t * K t) 9]
    convert ht using 1 <;> norm_num [Wu04Source.paperNode]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Wu04Source.node_left, Wu04Source.node_right]
  have he : cellLeft 1 k = upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [← he]
  exact profile_cell_integral z K le_rfl (upperNode_bounds 0).1 k

theorem original_basis_coefficient (k : Fin 9) {K : ℝ → ℝ}
    (hK : IntervalIntegrable K volume 1 3) :
    (∫ t in (1 : ℝ)..3, nineProfile (nodeBasis k) t * K t) =
      ∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1), K t := by
  classical
  rw [original_cell_decomposition _ hK]
  simp [nodeBasis, ite_mul]

theorem original_monotone_discretization {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    {K : ℝ → ℝ} (hK : IntervalIntegrable K volume 1 3)
    (hHK : IntervalIntegrable (fun t => wuImprovementLimit true δ t * K t) volume 1 3)
    (hpos : ∀ t ∈ Icc (1 : ℝ) 3, 0 ≤ K t) :
    (∑ k : Fin 9,
      (∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1), K t) *
        actualNine δ k) ≤
      ∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * K t := by
  simp_rw [mul_comm (∫ t in _.._, K t)]
  rw [← original_cell_decomposition _ hK]
  apply intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 3)
    (profile_mul_integrable _ hK) hHK
  intro t ht
  exact mul_le_mul_of_nonneg_right (nineProfile_le_actual hd hh ht) (hpos t ht)

theorem supported_weight_integrable {f w : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume 1 3) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hw : ContinuousOn w (Icc a b)) :
    IntervalIntegrable (fun t => f t * (Icc a b).indicator (fun _ => (1 : ℝ)) t * w t)
      volume 1 3 := by
  have hs : uIcc a b ⊆ uIcc (1 : ℝ) 3 := by
    rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Icc_subset_Icc ha hb
  have hw' : ContinuousOn w (uIcc a b) := by simpa [uIcc_of_le hab] using hw
  have hi := (hf.mono_set hs).mul_continuousOn hw'
  have hind : Integrable ((Icc a b).indicator (fun t => f t * w t)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi)
  convert hind.intervalIntegrable (a := 1) (b := 3) using 1
  ext t
  by_cases ht : t ∈ Icc a b <;> simp [ht]

end WuPaper.R2Matrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
