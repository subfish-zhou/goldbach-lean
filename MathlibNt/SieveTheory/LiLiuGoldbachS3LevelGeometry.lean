module

public import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairLevel

@[expose] public section

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The single cutoff pays the logarithmic loss and both natural rounding
boundaries, uniformly for every outer prime up to `N^(1/3)`. -/
theorem goldbachS3_level_eventually (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∀ p : ℕ, 0 < p →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      1 < LiuWeight.panModulusCutoff N B / p + 1 ∧
      ∀ ℓ ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).primeFactors,
        ℓ < LiuWeight.panModulusCutoff N B / p + 1 := by
  filter_upwards [goldbachOrderedPair_level_eventually B] with N hN
  refine ⟨hN.1, fun p hp hpu => hN.2 p hp (hpu.trans ?_)⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
