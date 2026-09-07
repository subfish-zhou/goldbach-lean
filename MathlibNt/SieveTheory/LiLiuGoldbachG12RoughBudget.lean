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

/-- Literal rough-boundary payment, uniform in epsilon and any grid satisfying the ratio. -/
theorem roughBoundary_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → ∀ ρ a ε : ℝ, 1 ≤ a →
      (∀ k ∈ indices ρ N, (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) →
      Real.log (N : ℝ)/(N : ℝ) *
        (400*∑ p ∈ roughBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤
          roughConstant*(a-1)+δ := by
  obtain ⟨K,hK,hb⟩ := nearMass_budget δ hδ
  refine ⟨K,hK,?_⟩
  intro N hN ρ a ε ha hmesh
  have hN1 : 1 ≤ N := by omega
  have hn : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left (roughBoundary_mass_le_nearMass hN1
    (by linarith : 0 < a) hmesh) hn).trans (hb N hN a ha)

/-- Actual rounded grid; cutoff precedes epsilon, which is unrestricted here. -/
theorem fixed_grid_roughBoundary_budget {ρ a : ℝ}
    (hρ : 1 < ρ) (hρa : ρ < a) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → ∀ ε : ℝ,
      Real.log (N : ℝ)/(N : ℝ) *
        (400*∑ p ∈ roughBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤
          roughConstant*(a-1)+δ := by
  obtain ⟨N₁,hN₁,hb⟩ := roughBoundary_budget δ hδ
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (ρ/(a-ρ)))
  obtain ⟨K,hK⟩ := eventually_atTop.mp hg
  refine ⟨max N₁ K,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN ε
  apply hb N ((le_max_left _ _).trans hN) ρ a ε (hρ.trans hρa).le
  intro k _
  apply short_ratio_of_rounding hρ hρa.le
  have hh : ρ/(a-ρ) ≤ (lowCut N : ℝ) :=
    (hK N ((le_max_right _ _).trans hN)).trans (Nat.le_ceil _)
  have hh' := (div_le_iff₀ (sub_pos.mpr hρa)).mp hh
  simpa only [mul_comm] using hh'

/-- The roughness constant itself is fixed before all grid parameters. -/
theorem exists_fixed_roughBoundary_constant : ∃ C > 0, ∀ ρ a : ℝ,
    1 < ρ → ρ < a → ∀ δ : ℝ, 0 < δ →
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → ∀ ε : ℝ,
      Real.log (N : ℝ)/(N : ℝ) *
        (400*∑ p ∈ roughBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤
          C*(a-1)+δ := by
  exact ⟨roughConstant,roughConstant_pos,fun _ _ hρ hρa δ hδ =>
    fixed_grid_roughBoundary_budget hρ hρa δ hδ⟩

/-- No physical pair is charged once per overlapping cell: the cells are disjoint. -/
theorem fullBoundary_sum_cells {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ)
    (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε), f p) =
      ∑ k ∈ indices ρ N, ∑ p ∈ boundaryCell ρ N ε k, f p := by
  apply sum_biUnion
  intro k _ l _ hkl
  exact (cell_disjoint hρ N ε hkl).mono sdiff_subset sdiff_subset

/-- Nonnegative union domination: no signed inclusion-exclusion is erased. -/
theorem fullBoundary_mass_le (ρ : ℝ) (N : ℕ) (ε : ℝ) :
    (∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε), goldbachG12NormalizedCoefficient N p.1) ≤
      (∑ p ∈ productBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) +
        ∑ p ∈ roughBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1 := by
  rw [boundary_union_decomposition]
  have h := sum_union_inter (s₁ := productBoundary ρ N ε) (s₂ := roughBoundary ρ N ε)
    (f := fun p : ℕ × ℕ => goldbachG12NormalizedCoefficient N p.1)
  have hn : 0 ≤ ∑ p ∈ productBoundary ρ N ε ∩ roughBoundary ρ N ε,
      goldbachG12NormalizedCoefficient N p.1 :=
    sum_nonneg (fun p _ => (goldbachG12NormalizedCoefficient_bounds N p.1).1)
  linarith

/-- Fixed universal constant includes the already paid product-boundary coefficient. -/
def fullConstant : ℝ := roughConstant + |(564383/1000000 : ℝ)*3*
  goldbachG12PrimeIntegral (fun _ => 1)|

theorem fullConstant_pos : 0 < fullConstant := by
  unfold fullConstant
  exact add_pos_of_pos_of_nonneg roughConstant_pos (abs_nonneg _)

/-- Full original raw boundary, not the output-prime weighted/signed remainder. -/
theorem fixed_grid_fullBoundary_budget {ρ a ε : ℝ}
    (hρ : 1 < ρ) (hρa : ρ < a) (ha2 : a ≤ 2) (he : 0 < ε) (he2 : ε ≤ 2/15)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N →
      Real.log (N : ℝ)/(N : ℝ) *
        (400*∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε),
          goldbachG12NormalizedCoefficient N p.1) ≤ fullConstant*(a-1)+δ := by
  obtain ⟨K₁,hK₁,hp⟩ := fixed_grid_productBoundary_integral_budget hρ hρa ha2 he he2
    (δ/2) (half_pos hδ)
  obtain ⟨K₂,_,hr⟩ := fixed_grid_roughBoundary_budget hρ hρa (δ/2) (half_pos hδ)
  refine ⟨max K₁ K₂,hK₁.trans (le_max_left _ _),?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hn : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) (Nat.cast_nonneg _)
  have hmass := mul_le_mul_of_nonneg_left (fullBoundary_mass_le ρ N ε)
    (show (0 : ℝ) ≤ 400 by norm_num)
  have hm := mul_le_mul_of_nonneg_left hmass hn
  have hp' := hp N ((le_max_left _ _).trans hN)
  have hr' := hr N ((le_max_right _ _).trans hN) ε
  have hc := mul_le_mul_of_nonneg_right
    (le_abs_self ((564383/1000000 : ℝ)*3*goldbachG12PrimeIntegral (fun _ => 1)))
    (sub_nonneg.mpr (hρ.trans hρa).le)
  unfold fullConstant
  nlinarith only [hm,hp',hr',hc]

/-- Headline quantifier order: the positive C is chosen before rho,a,epsilon,delta. -/
theorem exists_fixed_fullBoundary_constant : ∃ C > 0, ∀ ρ a ε : ℝ,
    1 < ρ → ρ < a → a ≤ 2 → 0 < ε → ε ≤ 2/15 → ∀ δ : ℝ, 0 < δ →
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N →
      Real.log (N : ℝ)/(N : ℝ) *
        (400*∑ p ∈ (indices ρ N).biUnion (boundaryCell ρ N ε),
          goldbachG12NormalizedCoefficient N p.1) ≤ C*(a-1)+δ := by
  exact ⟨fullConstant,fullConstant_pos,fun _ _ _ hρ hρa ha2 he he2 δ hδ =>
    fixed_grid_fullBoundary_budget hρ hρa ha2 he he2 δ hδ⟩

end G12RoughBoundary
