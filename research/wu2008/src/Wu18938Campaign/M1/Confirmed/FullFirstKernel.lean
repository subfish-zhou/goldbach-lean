import Wu18938Campaign.M1.Confirmed.FullSourceKernel

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullProfile

open Wu2008DoubleSieve Real Set MeasureTheory NodeExtension ActualNineFeedback FiniteProfile
open WuPaper.R2Matrix WuPaper.RMapMSigma
open scoped Classical Interval

theorem first_j_kernel_terminal (v : ℝ) : firstJKernel 3 3 v = 0 := by
  by_cases hv : v = 1
  · subst v
    norm_num [firstJKernel]
  · have hn : v ∉ Icc (1 : ℝ) 1 := by
      intro hh
      exact hv (le_antisymm hh.2 hh.1)
    have hi : (Icc (3 - 3 / 3 - 1 : ℝ) (3 - 2)).indicator
        (fun _ => (1 : ℝ)) v = 0 := by
      norm_num only [show (3 - 3 / 3 - 1 : ℝ) = 1 by norm_num,
        show (3 - 2 : ℝ) = 1 by norm_num]
      exact indicator_of_notMem hn _
    simp only [firstJKernel,show Real.log ((3 - 1) / (3 - 1) : ℝ) = 0 by norm_num,
      mul_zero,zero_add,hi,zero_div,zero_mul]

theorem first_j_original {H : ℝ → ℝ} (hH : Antitone H) (j : Fin 5) :
    lowerGainJ H (firstNode j) (firstS j) =
      ∫ v in (1 : ℝ)..3, H v * firstJKernel (firstNode j) (firstS j) v := by
  by_cases hj : j.val < 4
  · have hg := first_source63_geometry j hj
    have hS : 0 < firstS j := by have h := (first_geometry j).2.2.1; linarith
    unfold lowerGainJ
    rw [rationalWeight_rescale hg.1 hg.2.1 hg.2.2.1 hS]
    rw [(gProfile_weighted_formula hH.intervalIntegrable hg.1 hg.2.1
      hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2).2]
    exact source63_first_integral j hj hH.intervalIntegrable
  · have he : j = (4 : Fin 5) := Fin.ext (by omega)
    subst j
    rw [show firstNode (4 : Fin 5) = 3 by norm_num [firstNode],
      show firstS (4 : Fin 5) = 3 from rfl]
    simp only [lowerGainJ,intervalIntegral.integral_same,first_j_kernel_terminal,
      mul_zero,intervalIntegral.integral_zero]

theorem first_feedback_original {H : ℝ → ℝ} (hH : Antitone H) (j : Fin 5) :
    eProfile H (firstS j) + lowerGainJ H (firstNode j) (firstS j) / 2 =
      ∫ v in (1 : ℝ)..3, H v * Wu04Source.xi1 v (firstNode j) (firstS j) := by
  have hg := first_geometry j
  have hU := upperKernel_integrable hH.intervalIntegrable ⟨hg.2.2.1,hg.2.2.2.1⟩
  have hJ : IntervalIntegrable
      (fun v => H v * firstJKernel (firstNode j) (firstS j) v) volume 1 3 := by
    apply (((xi1_weighted_integrable j hH.intervalIntegrable).sub hU).const_mul 2).congr
    intro v hv
    have hv' : v ∈ Icc (1 : ℝ) 3 := by
      simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using uIoc_subset_uIcc hv
    dsimp only
    rw [xi1_split_original j hv']
    ring
  have he :
      (∫ v in (1 : ℝ)..3, H v * Wu04Source.xi1 v (firstNode j) (firstS j)) =
        ∫ v in (1 : ℝ)..3, H v * upperKernel (firstS j) v +
          (H v * firstJKernel (firstNode j) (firstS j) v) / 2 := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hv
    dsimp only
    rw [xi1_split_original j hv]
    ring
  rw [he,intervalIntegral.integral_add hU (hJ.div_const 2),intervalIntegral.integral_div,
    upperKernel_identity hH.intervalIntegrable ⟨hg.2.2.1,hg.2.2.2.1⟩,
    ← first_j_original hH j]

theorem first_gain_original_kernel {H : ℝ → ℝ} (hH : Antitone H)
    (j : Fin 5) (δ : ℝ) :
    FiniteProfile.firstGain δ (firstNode j) (firstS j) H =
      firstFunctionalGainPsi δ (firstNode j) (firstS j) +
        ∫ v in (1 : ℝ)..3, H v * sourceKernel ⟨j.val + 4,by omega⟩ v := by
  have hg := first_geometry j
  have hs : 2 < firstNode j := by
    dsimp [firstNode]
    linarith [Nat.cast_nonneg (α := ℝ) j.val]
  rw [first_gain_source_identity hH hs hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2,
    add_assoc,first_feedback_original hH j]
  have hk (v : ℝ) :
      sourceKernel ⟨j.val + 4,by omega⟩ v =
        Wu04Source.xi1 v (firstNode j) (firstS j) := by
    simp [sourceKernel]
  simp_rw [hk]

def sourceForcing (δ : ℝ) (j : Fin 9) : ℝ :=
  if h : j.val < 4 then
    coupledBase (coupledRow ⟨j.val,h⟩) - deltaLoss δ * coupledLoss (coupledRow ⟨j.val,h⟩)
  else firstFunctionalGainPsi δ (firstNode ⟨j.val - 4,by omega⟩)
    (firstS ⟨j.val - 4,by omega⟩)

theorem row_gain_original_kernel {H : ℝ → ℝ} (hH : Antitone H)
    (hHb : ∀ v, |H v| ≤ 1) (j : Fin 9) (δ : ℝ) (hδ : δ < 1 / 2) :
    rowGain δ H j = sourceForcing δ j + ∫ v in (1 : ℝ)..3, H v * sourceKernel j v := by
  unfold rowGain sourceForcing
  split_ifs with hj
  · exact second_gain_original_kernel hH hHb ⟨j.val,hj⟩ δ hδ
  · have hh := first_gain_original_kernel hH (⟨j.val - 4,by omega⟩ : Fin 5) δ
    simpa only [Fin.val_mk,Nat.sub_add_cancel (by omega : 4 ≤ j.val)] using hh

end Wu18938Campaign.M1.Confirmed.FullProfile
