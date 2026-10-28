import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughTransport

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12FineGrid

namespace G12RoughBoundary

/-- Chosen before all mesh, truncation and error parameters. -/
def roughConstant : ℝ := (53/2)*harmonicBound^3

theorem roughConstant_pos : 0 < roughConstant := by
  unfold roughConstant
  positivity [harmonicBound_pos]

/-- One common threshold works for every a≥1; the lattice endpoint is explicit. -/
theorem nearMass_uniform : ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → ∀ a : ℝ, 1 ≤ a →
    Real.log (N : ℝ)/(N : ℝ)*nearMass N a ≤
      roughConstant*((a-1)+1/((N : ℝ)^(4/53 : ℝ))) := by
  obtain ⟨K₁,hK₁,hc⟩ := cofactor_eventually
  obtain ⟨K₂,hh⟩ := harmonic_eventually
  refine ⟨max K₁ K₂,hK₁.trans (le_max_left _ _),?_⟩
  intro N hN a ha
  have hN4 : 4 ≤ N := by omega
  have hsum : Real.log (N : ℝ)/(N : ℝ)*nearMass N a ≤ (53/2 : ℝ)*nearReciprocal N a := by
    unfold nearMass nearReciprocal
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro v hv
    exact normalized_cofactor_le hN4 (mem_filter.mp hv).1
      (hc N ((le_max_left _ _).trans hN) v (mem_filter.mp hv).1)
  have hh' := pow_le_pow_left₀ (harmonic_nonneg N) (hh N ((le_max_right _ _).trans hN)) 3
  calc
    _ ≤ (53/2 : ℝ)*nearReciprocal N a := hsum
    _ ≤ (53/2 : ℝ)*(harmonic N^3*((a-1)+1/((N : ℝ)^(4/53 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (nearReciprocal_le (by omega) ha) (by norm_num)
    _ ≤ (53/2 : ℝ)*(harmonicBound^3*((a-1)+1/((N : ℝ)^(4/53 : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right hh' (add_nonneg (sub_nonneg.mpr ha) (by positivity))
    _ = _ := by unfold roughConstant; ring

/-- Error cutoff is independent of a, rho and epsilon. -/
theorem nearMass_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → ∀ a : ℝ, 1 ≤ a →
      Real.log (N : ℝ)/(N : ℝ)*nearMass N a ≤ roughConstant*(a-1)+δ := by
  obtain ⟨K₁,hK₁,hb⟩ := nearMass_uniform
  have ht := (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).comp
    tendsto_natCast_atTop_atTop).const_div_atTop roughConstant)
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max K₁ K₂,hK₁.trans (le_max_left _ _),?_⟩
  intro N hN a ha
  have hh := hb N ((le_max_left _ _).trans hN) a ha
  have he := hK₂ N ((le_max_right _ _).trans hN)
  dsimp only [Function.comp_apply] at he
  simp only [div_eq_mul_inv] at hh he ⊢
  nlinarith only [hh,he]


/-- No physical pair is charged once per overlapping cell: the cells are disjoint. -/
theorem fullBoundary_sum_cells {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ)
    (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε), f p) =
      ∑ k ∈ indices ρ N, ∑ p ∈ boundaryCell ρ N ε k, f p := by
  apply sum_biUnion
  intro k _ l _ hkl
  exact (cell_disjoint hρ N ε hkl).mono sdiff_subset sdiff_subset


/-- Fixed universal constant includes the already paid product-boundary coefficient. -/
def fullConstant : ℝ := roughConstant + |(564383/1000000 : ℝ)*3*
  goldbachG12PrimeIntegral (fun _ => 1)|

theorem fullConstant_pos : 0 < fullConstant := by
  unfold fullConstant
  exact add_pos_of_pos_of_nonneg roughConstant_pos (abs_nonneg _)


end G12RoughBoundary
