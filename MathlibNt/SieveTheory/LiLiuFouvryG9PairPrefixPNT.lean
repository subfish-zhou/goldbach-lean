import MathlibNt.SieveTheory.LiLiuFouvryG9PrefixWeights

noncomputable section
open Finset Filter
open LiLiuPrereqBuchstab
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Uniform prefix PNT and the exact logarithmic algebra assemble the genuine
relaxed kernel. No estimate is imposed on each individual third-prime box. -/
theorem fouvryG9WeightedPairPrefix_PNT {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ ρ δ : ℝ, 1 < ρ → δ < 1/4 →
      (∑ rs ∈ fouvryG9RelaxedPairs N ρ,
        fouvryG9FirstWeight N δ rs.1 * primePi (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2))) ≤
        ((1+ζ)*ρ^3*(N : ℝ)/Real.log (N : ℝ)^2)*fouvryG9RelaxedPairKernel N ρ δ := by
  obtain ⟨Y,_hY,hpnt⟩ := fouvryG9RectanglePrefix_uniform_PNT hζ
  obtain ⟨Ng,hg⟩ := eventually_atTop.1
    (g9Scale_eventually_const_mul_rpow_le Y 0 (1/3) (by norm_num))
  refine ⟨max 4 Ng,?_⟩
  intro N hN ρ δ hρ hδ
  have hN4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < (N : ℝ) := by linarith
  have hY : Y ≤ (N : ℝ)^(1/3 : ℝ) := by
    simpa using hg N ((le_max_right _ _).trans hN)
  unfold fouvryG9RelaxedPairKernel
  rw [mul_sum]
  apply sum_le_sum
  intro rs hrs
  obtain ⟨_,hn,hs,_,_,hslo,hcurve⟩ := mem_filter.mp hrs
  have hn0 : (0 : ℝ) < rs.1 := by exact_mod_cast hn.pos
  have hs0 : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hx : (rs.2 : ℝ) ≤ ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2) := by
    apply (le_div_iff₀ (mul_pos hn0 hs0)).mpr
    nlinarith only [hcurve]
  have hp := hpnt ((N : ℝ)^(1/3 : ℝ)) hY _ (hslo.trans hx)
  calc
    _ ≤ fouvryG9FirstWeight N δ rs.1 *
        ((1+ζ)*(ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2))/
          Real.log (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2))) := by
      apply mul_le_mul_of_nonneg_left _ (fouvryG9FirstWeight_nonneg hN1 hδ hrs)
      simpa only [mul_div_assoc] using hp
    _ = _ := fouvryG9RectanglePrefix_kernel_term hN1 (by linarith) hn.pos hs.pos δ ζ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
