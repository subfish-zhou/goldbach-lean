import MathlibNt.SieveTheory.LiLiuGoldbachG12GridAdmission

noncomputable section
open Real
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace G12FineGrid

/-- The source package is consumed at x=4MT for every atom in an occupied cell.
The single threshold precedes all meshes, cell indices and actual prime labels. -/
theorem uniform_occupied_source (δ : ℝ) (hδ : 0 < δ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1/100 ∧
      ∀ e η : ℝ, 0 < e → 0 < η → η < 1/8 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ρ : ℝ,
      1 < ρ → ρ ≤ 3/2 → ∀ k p : ℕ × ℕ,
      p ∈ motherCell ρ N e k →
      let x : ℝ := 4 * (longLower ρ k : ℝ) * shortLower ρ N k
      let T : ℝ := shortLower ρ N k
      SourceGeometry ρ N e k ∧
      1 < x ∧ 0 < T ∧ x ^ G12LocalScale.nu x T = T ∧
      ζ ≤ G12LocalScale.nu x T ∧ G12LocalScale.nu x T ≤ 1/10 + ζ/10 ∧
      (N : ℝ)^(1/3 : ℝ) ≤ G12LocalScale.level x T ζ ∧
      G12LocalScale.level x T ζ ≤ N ∧
      2 ≤ externalInternalLevel (G12LocalScale.level x T ζ) η ∧
      4/53 ≤ log (p.2 : ℝ) / log (N : ℝ) ∧
      log (p.2 : ℝ) / log (N : ℝ) ≤ 1/10 ∧
      4 * log (N : ℝ) / log (G12LocalScale.level x T ζ) ≤
        36 / (5 * (1 - log (p.2 : ℝ) / log (N : ℝ))) + δ := by
  obtain ⟨ζ,hζ,hζu,hs⟩ := G12LocalScale.uniform_source_package δ hδ
  refine ⟨ζ,hζ,hζu,?_⟩
  intro e η he hη hηu
  obtain ⟨A,hA⟩ := hs e η he hη hηu
  obtain ⟨B,hB,hg⟩ := uniform_occupied_geometry
  refine ⟨max A B,by omega,?_⟩
  intro N hN ρ hρ hρu k p hp
  have g := hg N (by omega) ρ e hρ hρu k ⟨p,hp⟩
  have hc := occupied_atom_coordinates hp
  refine ⟨g,?_⟩
  exact hA N (by omega) _ _ p.2 g.scale_lower g.scale_upper
    (by have hz := Real.rpow_nonneg (Nat.cast_nonneg N) (4/53 : ℝ); linarith [g.source_lower])
    (by exact_mod_cast hc.1.le) hc.2.2.1
    ((show (p.2 : ℝ) ≤ shortUpper ρ N k by exact_mod_cast hc.2.1).trans g.source_upper.le)

end G12FineGrid
