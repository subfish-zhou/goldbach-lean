import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKFloorReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKPartialSummation
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem wellFactorable_signedError_sq_le_floor_prefix_kscale
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε η : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4 * M * T z = x →
      ε ≤ ν → ν ≤ 1 / 10+ε/10 → T z = x ^ ν →
      ∀ U : Finset ℕ,
      (∀ m ∈ U, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      ∀ α c : ℕ → ℝ,
      (∀ m ∈ U, |α m| ≤ (fouvryTau i m : ℝ)) →
      SignedWellFactorable j (x ^ ((5 - 5 * ν) / 9 - ε)) c →
      let L := x ^ ((5 - 5 * ν) / 9 - ε)
      let R₀ := x ^ c2RExponent ν ε
      let S₀ := x ^ c2SExponent ν ε
      let J := Nat.log 2 ⌈L ^ 2 / M * x ^ η⌉₊
      R₀ * S₀ = L ∧
        ∃ γ ζ : ℕ → ℝ,
          factorSupported R₀ γ ∧ factorSupported S₀ ζ ∧
          (∀ r, |γ r| ≤ (fouvryTau j r : ℝ)) ∧
          (∀ s, |ζ s| ≤ (fouvryTau j s : ℝ)) ∧ c = factorConvolution γ ζ ∧
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
            ∃ b ≤ J, ∃ K ∈ wExtractedKeyBox (x ^ η),
              signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
                3072 * M * (∑ m ∈ U, α m ^ 2) * (J + 1 : ℕ) * (x ^ η) ^ 7 *
                  wAnalyticVariationConstant (Cscale*x ^ η) *
                  wAnalyticKeyPrefixMajorant
                    (wExtractedKeyFiber (wFloorCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b K)
                    K (betaClean (β z) a)
                    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a +
                  x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_floor_key_kscale
    (i := i) (j := j) A hSW hT hN hβ hCscale hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U hU α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha0 hax
  obtain ⟨b, hb, y, hy, K, hK, hk⟩ := ha a ha0 hax
  have hZ : 0 ≤ x ^ η := Real.rpow_nonneg (by linarith) η
  have hp := wExtractedFloorKeyExponential_norm_le_prefixes_kscale
    (Q := Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊)
    hCscale (lt_of_lt_of_le zero_lt_one hM) (lt_of_lt_of_le zero_lt_one (hT z)) hZ
    he.symm hy (fun n hn => (hN z n hn).1) (fun _ hq => (mem_Ioc.mp hq).1) hax
    (betaClean (β z) a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
    γ ζ (c2FiveSmallMask x η) (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε)
    (highOmegaCutoff x) b K
  refine ⟨b, hb, K, hK, hk.trans (add_le_add ?_ le_rfl)⟩
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 3072 * M * (∑ m ∈ U, α m ^ 2) *
      (Nat.log 2 ⌈(x ^ ((5 - 5 * ν) / 9 - ε)) ^ 2 / M * x ^ η⌉₊ + 1 : ℕ) *
        (x ^ η) ^ 7 from by positivity)
  convert hm using 1
  ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
