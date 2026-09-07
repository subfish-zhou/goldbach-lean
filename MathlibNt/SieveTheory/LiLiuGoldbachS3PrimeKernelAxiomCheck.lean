import MathlibNt.SieveTheory.LiLiuGoldbachS3RatioGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachS3PrimeKernel

open scoped BigOperators
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check (goldbachS3_sieveRatio : ℕ → ℝ → ℕ → ℝ)
#print axioms goldbachS3_sieveRatio

#check (goldbachS3_ratio_geometry :
  ∀ (B ξ : ℝ), 0 ≤ B → 0 < ξ →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) ≤ goldbachS3_sieveRatio N B p ∧
      goldbachS3_sieveRatio N B p ≤ 6 ∧
      |goldbachS3_sieveRatio N B p -
        ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| ≤ ξ)
#print axioms goldbachS3_ratio_geometry

#check (goldbachS3_ratio_range :
  ∀ B : ℝ, 0 ≤ B →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) ≤ goldbachS3_sieveRatio N B p ∧ goldbachS3_sieveRatio N B p ≤ 6)
#print axioms goldbachS3_ratio_range

#check (goldbachS3_primeKernelIntegral : ℝ → ℝ)
#print axioms goldbachS3_primeKernelIntegral

#check (goldbachS3_primeKernel_upper :
  ∀ (B β η : ℝ), 0 ≤ B → (4 / 53 : ℝ) < β → β ≤ (1 / 3 : ℝ) → 0 < η →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) / (p.totient : ℝ)) ≤
        goldbachS3_primeKernelIntegral β + η)
#print axioms goldbachS3_primeKernel_upper

#check (goldbachS3_unitKernel_upper :
  ∀ (β η : ℝ), (4 / 53 : ℝ) < β → 0 < η →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        (1 : ℝ) / (p.totient : ℝ)) ≤ Real.log (β / (4 / 53 : ℝ)) + η)
#print axioms goldbachS3_unitKernel_upper

example (N : ℕ) (B : ℝ) (p : ℕ) :
    goldbachS3_sieveRatio N B p =
      Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
        Real.log ((N : ℝ) ^ (4 / 53 : ℝ)) := rfl

example (β : ℝ) :
    goldbachS3_primeKernelIntegral β =
      ∫ u in (4 / 53 : ℝ)..β,
        suzukiContinuousUpperFactor (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ)) / u := rfl

example (B ξ : ℝ) (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, 1 ≤ p →
      (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      0 < ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) ∧
      (3 / 2 : ℝ) ≤
        Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
          Real.log ((N : ℝ) ^ (4 / 53 : ℝ)) ∧
      Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
          Real.log ((N : ℝ) ^ (4 / 53 : ℝ)) ≤ 6 ∧
      |Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
          Real.log ((N : ℝ) ^ (4 / 53 : ℝ)) -
        ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| ≤ ξ := by
  exact goldbachS3_ratio_geometry B ξ hB hξ

example (B η : ℝ) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        suzukiContinuousUpperFactor
          (Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
            Real.log ((N : ℝ) ^ (4 / 53 : ℝ))) / (p.totient : ℝ)) ≤
        (∫ u in (4 / 53 : ℝ)..(1 / 3 : ℝ),
          suzukiContinuousUpperFactor (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ)) / u) + η := by
  exact goldbachS3_primeKernel_upper B (1 / 3) η hB (by norm_num) le_rfl hη

example (B η : ℝ) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)),
        suzukiContinuousUpperFactor
          (Real.log ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ) /
            Real.log ((N : ℝ) ^ (4 / 53 : ℝ))) / (p.totient : ℝ)) ≤
        (∫ u in (4 / 53 : ℝ)..(3 / 11 : ℝ),
          suzukiContinuousUpperFactor (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ)) / u) + η := by
  exact goldbachS3_primeKernel_upper B (3 / 11) η hB (by norm_num) (by norm_num) hη

example (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), (1 : ℝ) / (p.totient : ℝ)) ≤
        Real.log ((1 / 3 : ℝ) / (4 / 53 : ℝ)) + η := by
  exact goldbachS3_unitKernel_upper (1 / 3) η (by norm_num) hη

example (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (3 / 11 : ℝ)), (1 : ℝ) / (p.totient : ℝ)) ≤
        Real.log ((3 / 11 : ℝ) / (4 / 53 : ℝ)) + η := by
  exact goldbachS3_unitKernel_upper (3 / 11) η (by norm_num) hη

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig