import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFullLevelDomain
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFourierIntegral

/-!
# Analytic reduction of the original C.2 error on its full modulus range

The well-factorable factors are selected before the varying residue. The
dyadic block is selected afterwards from the actual retained frequencies.
Neither the first signed coefficient nor the real Fourier factor is
replaced by a pointwise absolute-value majorant.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The actual dyadic exponential piece after removing the Fourier
transform. Its signed coefficients and every original fiber mask remain
inside the sum; the integration variable is the original real variable. -/
def wExtractedBlockExponential (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop)
    (R S ξ : ℝ) (b : ℕ) (u : ℝ) : ℂ :=
  wFourierExponentialSum
    (frequencyBlock (wExtractedFrequencies H N Q a P R S ξ) Prod.snd b)
    (fun t => wExtractedCoefficient β c₁ γ ζ t.1) a
    (fun t => (wExtractedOriginal t.1).1.1)
    (fun t => (wExtractedOriginal t.1).1.2)
    (fun t => (wExtractedOriginal t.1).2.1)
    (fun t => (wExtractedOriginal t.1).2.2) Prod.snd u


theorem wExtractedFrequencyBlock_le_max {M : ℝ} (hM : 0 < M)
    (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop)
    (R S ξ : ℝ) (b : ℕ) :
    ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
      (∀ z ∈ Set.Icc (1 / 2 : ℝ) 3,
        ‖wExtractedBlockExponential H N Q β c₁ γ ζ a P R S ξ b (M * z)‖ ≤
          ‖wExtractedBlockExponential H N Q β c₁ γ ζ a P R S ξ b (M * y)‖) ∧
      ‖∑ t ∈ frequencyBlock (wExtractedFrequencies H N Q a P R S ξ) Prod.snd b,
        wExtractedFrequencyTerm M β c₁ γ ζ a t‖ ≤
          3 * M * ‖wExtractedBlockExponential H N Q β c₁ γ ζ a P R S ξ b (M * y)‖ := by
  exact norm_sum_wPoissonFrequency_le_three_mul_max hM _ _ _ _ _ _ _ _
    (fun _ ht => (Finset.mem_filter.mp ht).2.1)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
