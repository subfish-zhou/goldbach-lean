import W01ContinuousCount

noncomputable section
namespace WuTarget.E04Continuous
open Set MeasureTheory QuarterTrim NodeExtension ActualNineFeedback W01Continuous
open scoped Classical

theorem first_profile (w : Fin 21 → ℝ) {s : ℝ}
    (hs : 2 < s ∧ s ≤ 21/10) :
    DirectFiniteF6.profile w s = w 0 := by
  change Wu08Staircase.eval
    ((2,21/10,w 0) :: (List.finRange 21).tail.map (DirectFiniteF6.row w)) s = w 0
  exact Wu08Staircase.eval_hit _ _ _ _ _ hs

theorem first_cell_surplus {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {s : ℝ} (hs : 2 < s ∧ s ≤ 41/20) :
    x 0/22 ≤ hContinuous x s -
      DirectFiniteF6.profile (matrixApply transferMatrix x) s := by
  have hi := upperProfile_div_integrable x
  have hab : s-1 ≤ (11/10 : ℝ) := by linarith [hs.2]
  have hlo (t : ℝ) (ht : t ∈ Icc (s-1) (11/10)) :
      x 0*(10/11) ≤ upperProfile x t/t := by
    have ht0 : 0 < t := by linarith [hs.1,ht.1]
    rw [upperProfile_initial x
      (show t ∈ Icc 1 (rNode 2) by
        norm_num [rNode]; exact ⟨by linarith [hs.1,ht.1],by linarith [ht.2]⟩)]
    apply (le_div_iff₀ ht0).mpr
    have := mul_le_mul_of_nonneg_left ht.2 (hx 0)
    nlinarith only [this]
  have hm := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := x 0*(10/11))) hi.intervalIntegrable hlo
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  have hj := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := s-1) (b := 11/10))
    (hi.intervalIntegrable (a := 11/10) (b := rNode 29))
  have hn : hContinuous x (21/10) = matrixApply transferMatrix x 0 := by
    simpa [rNode] using hContinuous_node x 0
  rw [first_profile _ ⟨hs.1,by linarith [hs.2]⟩,← hn]
  have he : hContinuous x s - hContinuous x (21/10) =
      ∫ t in (s-1)..(11/10), upperProfile x t/t := by
    have heq : (21/10 : ℝ)-1 = 11/10 := by norm_num
    unfold hContinuous
    rw [heq]
    linarith only [hj]
  rw [he]
  have hp := mul_nonneg (hx 0) (show 0 ≤ 41/20-s by linarith [hs.2])
  nlinarith only [hm,hp]

def rectangle : Set (ℝ × ℝ) :=
  Icc (1/10) (51/500) ×ˢ Icc (123/500) (247/1000)

theorem rectangle_geometry {v : ℝ × ℝ} (hv : v ∈ rectangle) :
    v ∈ StaircaseShrink.domain 0 ∧
    (2 < u v.1 v.2 ∧ u v.1 v.2 ≤ 41/20) ∧
    (0 < v.1*v.2*(1/2-v.1-v.2) ∧ v.1*v.2*(1/2-v.1-v.2) ≤ 1/250) := by
  rcases hv with ⟨⟨ha,hb⟩,hc,hd⟩
  have hdom : v ∈ StaircaseShrink.domain 0 := by
    rw [StaircaseShrink.domain_iff]
    norm_num [alpha,beta]
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  refine ⟨hdom,?_,(DirectFiniteF6.denominator_bounds hdom).1,?_⟩
  · unfold u
    rw [lt_div_iff₀ alpha_pos,div_le_iff₀ alpha_pos]
    norm_num [alpha]
    exact ⟨by linarith,by linarith⟩
  · have hv0 : 0 ≤ v.1 := by linarith
    have hp := mul_le_mul hb hd (by linarith : 0 ≤ v.2) (by norm_num : (0:ℝ) ≤ 51/500)
    have hz : 1/2-v.1-v.2 ≤ (77/500 : ℝ) := by linarith
    have hq := mul_le_mul hp hz (by linarith : 0 ≤ 1/2-v.1-v.2)
      (by norm_num : (0:ℝ) ≤ (51/500)*(247/1000))
    norm_num at hq
    linarith only [hq]

theorem rectangle_kernel_surplus {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {v : ℝ × ℝ} (hv : v ∈ rectangle) :
    125*x 0/11 ≤ continuousUniform x 0 v -
      DirectFiniteF6.uniform (matrixApply transferMatrix x) 0 v := by
  obtain ⟨hd,hs,hpos,hupper⟩ := rectangle_geometry hv
  have h := first_cell_surplus hx hs
  rw [continuousUniform,DirectFiniteF6.uniform,if_pos hd,if_pos hd]
  unfold kernel
  rw [← sub_div,le_div_iff₀ hpos]
  have hm := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ 125*x 0/11 by positivity)
  nlinarith only [h,hm]

end WuTarget.E04Continuous
