import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKFactored
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDelayedFactorExtraction
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem wellFactorable_signedError_sq_le_five_small_extracted_kscale
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε η : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4 * M * T z = x →
      ε ≤ ν → ν ≤ 1 / 10+ε/10 → T z = x ^ ν →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊ →
      ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      SignedWellFactorable j (x ^ ((5 - 5 * ν) / 9 - ε)) c →
      let R₀ := x ^ c2RExponent ν ε
      let S₀ := x ^ c2SExponent ν ε
      R₀ * S₀ = x ^ ((5 - 5 * ν) / 9 - ε) ∧
        ∃ γ ζ : ℕ → ℝ,
          factorSupported R₀ γ ∧ factorSupported S₀ ζ ∧
          (∀ r, |γ r| ≤ (fouvryTau j r : ℝ)) ∧
          (∀ s, |ζ s| ≤ (fouvryTau j s : ℝ)) ∧ c = factorConvolution γ ζ ∧
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
          signedError S (N z) Q α (β z) c a ^ 2 ≤
            8 * (∑ m ∈ S, α m ^ 2) *
              wMaskedFactorExtractedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
                (betaClean (β z) a)
                (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) +
              x ^ 2 / Real.log x ^ A := by
  simpa only [c2FiveSmall_factored_eq_extracted] using
    (wellFactorable_signedError_sq_le_five_small_factored_kscale
      (i := i) (j := j) A hSW hT hN hβ hCscale hε hη)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
