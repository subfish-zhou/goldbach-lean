import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidSafeCell

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SafeGridBudget

/-- The actual log-squared number of grid cells costs three fixed log powers,
including its rho-dependent constant. Rho is fixed before the threshold. -/
theorem grid_fee (ρ : ℝ) (hρ : 1 < ρ) (B : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((G12FineGrid.indices ρ N).card : ℝ)*(N/Real.log (N : ℝ)^(B+3)) ≤
        N/Real.log (N : ℝ)^B := by
  filter_upwards [absorb_constant ((1/Real.log ρ+2)^2) B,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)] with N ha hl
  have hl1 : 1 ≤ Real.log (N : ℝ) := hl
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have hc := indices_card_log hρ hl1
  calc
    _ ≤ ((1/Real.log ρ+2)^2*Real.log (N : ℝ)^2)*(N/Real.log (N : ℝ)^(B+3)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (1/Real.log ρ+2)^2*(N/Real.log (N : ℝ)^(B+1)) := by
      rw [show B+3 = (B+1)+2 by omega, pow_add]
      field_simp
    _ ≤ _ := ha

/-- Fixed-grid output with arbitrary logarithmic saving, the true author weight
inside the original normalized coefficient sum, and no unpaid additive remainder. -/
theorem fixed_grid_paid (δ : ℝ) (hδ : 0 < δ) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (ρ : ℝ) (hρ : 1 < ρ) (hρu : ρ ≤ 3/2) (B : ℕ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N →
      (∑ k ∈ G12FineGrid.indices ρ N, originalOutput N (G12FineGrid.safe ρ N e k)) ≤
        400*(∑ k ∈ G12FineGrid.indices ρ N, authorMass N (G12FineGrid.safe ρ N e k) δ)*
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ) + N/Real.log (N : ℝ)^B := by
  obtain ⟨J,hJ,hj⟩ := safe_cell_paid δ hδ e he he1 (B+3)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (grid_fee ρ hρ B)
  refine ⟨max J L,hJ.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hh := sum_cell_bounds (G12FineGrid.indices ρ N)
    (fun k => originalOutput N (G12FineGrid.safe ρ N e k))
    (fun k => 400*authorMass N (G12FineGrid.safe ρ N e k) δ *
      SingularSeries.liuSingularSeries N/Real.log (N : ℝ))
    (N/Real.log (N : ℝ)^(B+3))
    (fun k _ => hj N ((le_max_left _ _).trans hN) hEven ρ hρ hρu k)
  have hf := hL N ((le_max_right _ _).trans hN)
  have heq :
      (∑ k ∈ G12FineGrid.indices ρ N,
        400*authorMass N (G12FineGrid.safe ρ N e k) δ *
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ)) =
      400*(∑ k ∈ G12FineGrid.indices ρ N, authorMass N (G12FineGrid.safe ρ N e k) δ)*
        SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
    simp only [mul_sum, sum_mul, sum_div]
  rw [heq] at hh
  exact hh.trans (add_le_add le_rfl hf)

/-- Final safe-grid bound at singular-series scale. The main slack and additive
slack can be chosen independently; neither depends on N or the cell index. -/
theorem fixed_grid_normalized (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (ρ : ℝ) (hρ : 1 < ρ) (hρu : ρ ≤ 3/2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, Even N →
      (∑ k ∈ G12FineGrid.indices ρ N, originalOutput N (G12FineGrid.safe ρ N e k)) ≤
        400*(∑ k ∈ G12FineGrid.indices ρ N, authorMass N (G12FineGrid.safe ρ N e k) δ)*
          SingularSeries.liuSingularSeries N/Real.log (N : ℝ) +
        τ*(SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨J,hJ,hj⟩ := fixed_grid_paid δ hδ e he he1 ρ hρ hρu 3
  obtain ⟨L,hL⟩ := eventually_atTop.mp (goldbachBV_logCube_normalized 1 τ hτ)
  refine ⟨max J L,hJ.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hh := hj N ((le_max_left _ _).trans hN) hEven
  have hf := hL N ((le_max_right _ _).trans hN)
  simp only [one_mul] at hf
  exact hh.trans (add_le_add le_rfl hf)

end G12SafeGridBudget
