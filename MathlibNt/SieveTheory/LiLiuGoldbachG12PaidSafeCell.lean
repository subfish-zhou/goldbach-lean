import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernel

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SafeGridBudget

/-- The original continuous clipped author weight is monotone, including its join. -/
theorem author_monotone : Monotone goldbachG11AuthorWeight := by
  intro a b hab
  unfold goldbachG11AuthorWeight
  have hm : min a (1/10 : ℝ) ≤ min b (1/10 : ℝ) := min_le_min_right _ hab
  have hb : min b (1/10 : ℝ) ≤ 1/10 := min_le_right _ _
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

def authorMass (N : ℕ) (A : Finset (ℕ × ℕ)) (δ : ℝ) : ℝ :=
  ∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1 *
    (goldbachG11AuthorWeight (Real.log p.2 / Real.log N) + δ)

def originalOutput (N : ℕ) (A : Finset (ℕ × ℕ)) : ℝ :=
  400*∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1*
    (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)

theorem authorMass_empty (N : ℕ) (δ : ℝ) : authorMass N ∅ δ = 0 := by
  simp [authorMass]

theorem originalOutput_empty (N : ℕ) : originalOutput N ∅ = 0 := by
  simp [originalOutput]

theorem endpoint_author_comparison {N T : ℕ} (hN : 4 ≤ N) (hT : 1 ≤ T)
    (hThi : (T : ℝ) ≤ (N : ℝ)^(1/10 : ℝ)) (A : Finset (ℕ × ℕ)) (δ : ℝ)
    (hA : ∀ p ∈ A, T ≤ p.2) :
    (36/(5*(1-Real.log T/Real.log N))+δ)*G12FlexibleWF.mass N A ≤
      authorMass N A δ := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have ht : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hu : Real.log (T : ℝ)/Real.log N ≤ 1/10 := by
    apply (div_le_iff₀ hl).mpr
    have hh := Real.log_le_log ht hThi
    rw [Real.log_rpow (by linarith : (0 : ℝ) < N)] at hh
    linarith
  rw [← goldbachG11AuthorWeight_eq_low hu]
  unfold G12FlexibleWF.mass authorMass
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hc := (goldbachG12NormalizedCoefficient_bounds N p.1).1
  have hlog := Real.log_le_log ht (show (T : ℝ) ≤ p.2 by exact_mod_cast hA p hp)
  have hw := author_monotone (div_le_div_of_nonneg_right hlog hl.le)
  nlinarith

/-- Real safe cells, with empty cells handled separately and all occupied endpoint
conditions supplied by GridAdmission. No caller-provided per-cell size hypothesis. -/
theorem safe_cell_paid (δ : ℝ) (hδ : 0 < δ) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) (B : ℕ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N → ∀ ρ : ℝ,
      1 < ρ → ρ ≤ 3/2 → ∀ k : ℕ × ℕ,
      originalOutput N (G12FineGrid.safe ρ N e k) ≤
        400*authorMass N (G12FineGrid.safe ρ N e k) δ *
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ) + N/Real.log (N : ℝ)^B := by
  obtain ⟨_,_,_,_,h⟩ := exists_rectangle_paid
  obtain ⟨_,_,_,_,_,_,h⟩ := h δ hδ
  obtain ⟨J,hJ,hj⟩ := h e he he1 B
  obtain ⟨L,_,hg⟩ := G12FineGrid.uniform_occupied_geometry
  refine ⟨max J L,hJ.trans (le_max_left _ _),?_⟩
  intro N hN hEven ρ hρ hρu k
  have hN4 : 4 ≤ N := hJ.trans ((le_max_left _ _).trans hN)
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  by_cases hne : (G12FineGrid.safe ρ N e k).Nonempty
  · have hm : (G12FineGrid.motherCell ρ N e k).Nonempty :=
      hne.mono (G12FineGrid.safe_subset ρ (by omega) e k)
    have g := hg N ((le_max_right _ _).trans hN) ρ e hρ hρu k hm
    have hout := hj N ((le_max_left _ _).trans hN) hEven
      (G12FineGrid.longLower ρ k) (G12FineGrid.longUpper ρ N k)
      (G12FineGrid.shortLower ρ N k) (G12FineGrid.shortUpper ρ N k)
      (by linarith [g.long_three]) g.long_order g.long_twice
      (by linarith [g.short_three]) g.short_order g.short_twice
      g.source_lower g.source_upper g.scale_lower g.scale_upper e
    have hThi : (G12FineGrid.shortLower ρ N k : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) :=
      (show (G12FineGrid.shortLower ρ N k : ℝ) ≤ G12FineGrid.shortUpper ρ N k by
        exact_mod_cast g.short_order).trans g.source_upper.le
    have hcmp := endpoint_author_comparison hN4 (by linarith [g.short_three]) hThi
      (G12FineGrid.safe ρ N e k) δ (fun p hp =>
        (G12FineGrid.occupied_atom_coordinates
          (G12FineGrid.safe_subset ρ (by omega) e k hp)).1.le)
    have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcmp
      (by norm_num : (0 : ℝ) ≤ 400))
      (div_nonneg (SingularSeries.liuSingularSeries_pos N).le hl)
    dsimp only at hout
    change originalOutput N (G12FineGrid.safe ρ N e k) ≤ _ at hout
    have hmain' :
        (36/(5*(1-Real.log (G12FineGrid.shortLower ρ N k)/Real.log N))+δ)*400*
          G12FlexibleWF.mass N (G12FineGrid.safe ρ N e k)*
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ) ≤
        400*authorMass N (G12FineGrid.safe ρ N e k) δ *
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
      simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hmain
    exact hout.trans (add_le_add hmain' le_rfl)
  · have hempty := not_nonempty_iff_eq_empty.mp hne
    rw [hempty,originalOutput_empty,authorMass_empty]
    simp only [mul_zero,zero_mul,zero_div,zero_add]
    positivity

/-- Exact slack ledger: the delta contribution is delta times the original mass. -/
theorem authorMass_slack (N : ℕ) (A : Finset (ℕ × ℕ)) (δ : ℝ) :
    authorMass N A δ = authorMass N A 0 + δ*G12FlexibleWF.mass N A := by
  simp only [authorMass, G12FlexibleWF.mass, mul_add, sum_add_distrib, add_zero]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

end G12SafeGridBudget
