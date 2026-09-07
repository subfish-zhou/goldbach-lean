import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedPrefix
import MathlibNt.SieveTheory.LiLiuFouvryG9PairPrefixPNT

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Complete actual occupied weighted-mass bound, with the original Qk and
one prime prefix per pair. All finite and analytic weight inputs are supplied. -/
theorem fouvryG9RectangleMass_le_kernel {e ρ δ ζ : ℝ}
    (he : 0 < e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hδ : δ < 1/4) (hζ : 0 < ζ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      (∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9RectangleMass N ρ k /
        Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ)))) ≤
        ((1+ζ)*ρ^3*(N : ℝ)/Real.log (N : ℝ)^2)*fouvryG9RelaxedPairKernel N ρ δ := by
  obtain ⟨Np,hp⟩ := fouvryG9WeightedPairPrefix_PNT hζ
  obtain ⟨Ng,hg⟩ := eventually_atTop.1
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  refine ⟨max Np (max Ng 4),?_⟩
  intro N hN
  have hNp := (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hNg := (le_max_left _ _).trans hr
  have hN4 : (4 : ℝ) ≤ N := (le_max_right _ _).trans hr
  have hN1 : 1 < (N : ℝ) := by linarith
  have hsix : 6 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hg N hNg
  have hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1 := by
    intro k hk
    have hg := fouvryG9Grid_buffered_geometry he hρ hρu (fouvryG9GridCell_nonempty_iff.mpr hk)
    dsimp only at hg
    linarith [hg.2.2.2.1]
  have hw := fouvryG9WeightedPrefix_le_primePi (by exact_mod_cast hN1.le) hρ hρu hbig
    (fun k => 1/Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))))
    (fouvryG9FirstWeight N δ) (fun _ hrs => fouvryG9FirstWeight_nonneg hN1 hδ hrs)
    (fun _ _ _ hn => fouvryG9RectanglePrefix_log_weight hN1 hρ hδ hn)
  have hleft : (∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9RectangleMass N ρ k /
      Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ)))) =
      ∑ k ∈ fouvryG9GridUsed N e ρ,
        (1/Real.log ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))))*
          fouvryG9RectangleMass N ρ k := by
    apply sum_congr rfl
    intro k _
    ring
  rw [hleft]
  exact hw.trans (hp N hNp ρ δ hρ hδ)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
