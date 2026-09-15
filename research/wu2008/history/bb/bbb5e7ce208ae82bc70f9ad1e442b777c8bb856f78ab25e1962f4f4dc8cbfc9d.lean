import SrcSixthGainRoot

noncomputable section
namespace WuSource.SrcSixthGain.Analytic
open Real Set Wu2008DoubleSieve QuarterTrim
open scoped Classical

theorem source_box_first_ceiling {N k : ℕ} {delta Delta x y : ℝ}
    (hN : 1 < N)
    (hb : wuSourceBox k delta N 2 Delta ![(N : ℝ)^y,(N : ℝ)^x]) :
    y ≤ (1/2-delta)/2 := by
  have hp := hb.2.2.2.2.2 (0 : Fin 2)
  have hR : (1 : ℝ) < N := by exact_mod_cast hN
  have he : ((N : ℝ)^y)^2 = (N : ℝ)^(2*y) := by
    rw [← rpow_two,← rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  norm_num at hp
  rw [he,rpow_le_rpow_left_iff hR] at hp
  linarith only [hp]

theorem source_box_iff_exact_boundary {N : ℕ} {delta Delta x y : ℝ}
    (hN : 1 < N) (hd : 0 < delta) (hdhi : delta < 1/100)
    (hlo : 1+log (N : ℝ)^(-4 : ℝ) ≤ Delta)
    (hhi : Delta < 1+2*log (N : ℝ)^(-4 : ℝ))
    (hr : truncatedSixthLowerRegion delta x y) :
    wuSourceBox 2 delta N 2 Delta ![(N : ℝ)^y,(N : ℝ)^x] ↔
      y ≤ (1/2-delta)/2 := by
  constructor
  · exact source_box_first_ceiling hN
  · intro hy
    exact truncatedSixthLower_source_box hN.le hd hdhi hlo hhi ⟨hr,hy⟩

theorem source_depth_cannot_remove_boundary {N : ℕ} {delta Delta x y : ℝ}
    (hN : 1 < N) (hy : (1/2-delta)/2 < y) :
    ∀ k : ℕ, ¬ wuSourceBox k delta N 2 Delta ![(N : ℝ)^y,(N : ℝ)^x] := by
  intro k hb
  exact (not_le_of_gt hy) (source_box_first_ceiling hN hb)

theorem high_triangle_source_parameter {delta x y : ℝ}
    (hd : 0 ≤ delta) (hr : truncatedSixthLowerRegion delta x y)
    (hy : 1/4 < y) :
    2 ≤ truncatedSixthLowerS delta x y ∧
      truncatedSixthLowerS delta x y < 927/400-delta/alpha := by
  refine ⟨(truncatedSixthLower_region_bounds hd hr).2.2.2.1,?_⟩
  have hx := hr.1
  norm_num [truncatedSixthLowerS,truncatedSixthLowerC,truncatedSixthLowerAlpha,alpha] at hx ⊢
  linarith only [hx,hy]

theorem fourth_cell_boundary :
    (23/10 : ℝ) < 927/400 ∧ (927/400 : ℝ) < 24/10 := by
  norm_num

theorem moving_boundary_partition {delta x y : ℝ}
    (hr : truncatedSixthLowerRegion delta x y) :
    truncatedSixthLowerAdmissibleRegion delta x y ∨
      ((1/2-delta)/2 < y ∧ y ≤ 1/4) ∨
      (1/4 < y) := by
  by_cases hy : y ≤ (1/2-delta)/2
  · exact Or.inl ⟨hr,hy⟩
  · by_cases hy' : y ≤ 1/4
    · exact Or.inr (Or.inl ⟨lt_of_not_ge hy,hy'⟩)
    · exact Or.inr (Or.inr (lt_of_not_ge hy'))

theorem boundary_strip_width {delta y : ℝ}
    (hy : (1/2-delta)/2 < y) (hy' : y ≤ 1/4) :
    0 ≤ 1/4-y ∧ 1/4-y < delta/2 := by
  constructor <;> linarith

#print axioms source_box_iff_exact_boundary
#print axioms source_depth_cannot_remove_boundary
#print axioms high_triangle_source_parameter
end WuSource.SrcSixthGain.Analytic
