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

theorem wExtractedFrequencyBlock_eq_integral {M : ℝ} (hM : 0 < M)
    (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop)
    (R S ξ : ℝ) (b : ℕ) :
    (∑ t ∈ frequencyBlock (wExtractedFrequencies H N Q a P R S ξ) Prod.snd b,
      wExtractedFrequencyTerm M β c₁ γ ζ a t) =
      ∫ u : ℝ, (scaledDyadicCutoff M u : ℂ) *
        wExtractedBlockExponential H N Q β c₁ γ ζ a P R S ξ b u := by
  exact sum_wPoissonFrequency_eq_integral hM _ _ _ _ _ _ _ _
    (fun _ ht => (Finset.mem_filter.mp ht).2.1)

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

theorem wMaskedFactorExtractedTruncated_fullLevel_dyadic_bound
    {M Z L : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (N : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    ∃ j ≤ Nat.log 2 ⌈L ^ 2 / M * Z⌉₊,
      |wMaskedFactorExtractedTruncated M (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊)
        β c₁ γ ζ a P R S ξ| ≤
        (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
          ‖∑ t ∈ frequencyBlock
            (wExtractedFrequencies (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊) a P R S ξ)
              Prod.snd j, wExtractedFrequencyTerm M β c₁ γ ζ a t‖ := by
  obtain ⟨j, hj, hb⟩ := wMaskedFactorExtractedTruncated_dyadic_bound
    M (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a P R S ξ
  have hlog := Nat.log_mono_right (b := 2)
    (wExtractedMaxFrequency_le_fullLevel hM hZ hL N a P R S ξ)
  refine ⟨j, hj.trans hlog, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact_mod_cast Nat.add_le_add_right hlog 1

/-- A quantitative integral-to-maximum bound for the current extracted W,
on the genuine full-level modulus interval. There is no supplied upper
bound or cancellation hypothesis for the selected exponential piece. -/
theorem wMaskedFactorExtractedTruncated_fullLevel_exponential_bound
    {M Z L : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (N : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    ∃ b ≤ Nat.log 2 ⌈L ^ 2 / M * Z⌉₊, ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
      |wMaskedFactorExtractedTruncated M (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊)
        β c₁ γ ζ a P R S ξ| ≤
        3 * M * (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
          ‖wExtractedBlockExponential (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊)
            β c₁ γ ζ a P R S ξ b (M * y)‖ := by
  obtain ⟨b, hb, he⟩ := wMaskedFactorExtractedTruncated_fullLevel_dyadic_bound
    hM hZ hL N β c₁ γ ζ a P R S ξ
  obtain ⟨y, hy, _, hmax⟩ := wExtractedFrequencyBlock_le_max
    hM (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a P R S ξ b
  refine ⟨b, hb, y, hy, he.trans ?_⟩
  calc
    _ ≤ (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
        (3 * M * ‖wExtractedBlockExponential (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊)
          β c₁ γ ζ a P R S ξ b (M * y)‖) :=
      mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
    _ = _ := by ring

/-- No modulus-subset parameter occurs at this analytic endpoint.
The scale-only number of shells is explicit and the original signed
error, full WF weight, and original SW family remain on the left. -/
theorem wellFactorable_signedError_sq_le_fullLevel_dyadic_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4 * M * T z = x →
      ε ≤ ν → ν ≤ 1 / 10 → T z = x ^ ν →
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
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
            ∃ b ≤ J,
              signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
                8 * (∑ m ∈ U, α m ^ 2) * (J + 1 : ℕ) *
                  ‖∑ t ∈ frequencyBlock
                    (wExtractedFrequencies (wUniformCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x))
                    Prod.snd b,
                    wExtractedFrequencyTerm M (betaClean (β z) a)
                      (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                      γ ζ a t‖ +
                  x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_five_small_extracted_c2
    (i := i) (j := j) A hSW hT hN hβ hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U
      (Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊) hU (Subset.refl _) α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha0 hax
  obtain ⟨b, hb, hbound⟩ := wMaskedFactorExtractedTruncated_fullLevel_dyadic_bound
    (lt_of_lt_of_le (by norm_num) hM) (Real.rpow_nonneg (by linarith : 0 ≤ x) η)
    (Real.rpow_nonneg (by linarith : 0 ≤ x) ((5 - 5 * ν) / 9 - ε))
    (N z) (betaClean (β z) a)
    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a
    (c2FiveSmallMask x η) (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε)
    (highOmegaCutoff x)
  refine ⟨b, hb, (ha a ha0 hax).trans ?_⟩
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ 8 * (∑ m ∈ U, α m ^ 2) *
        |wMaskedFactorExtractedTruncated M (wUniformCutoff M (x ^ η)) (N z)
          (Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊) (betaClean (β z) a)
          (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a
          (c2FiveSmallMask x η) (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε)
          (highOmegaCutoff x)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hbound
          (show 0 ≤ 8 * (∑ m ∈ U, α m ^ 2) from by positivity)

/-- Original C.2 error reduced to an attained, explicitly constructed
exponential piece. The threshold still precedes the family index,
nu, scales and residue; the legitimate WF factors still precede a.
This is not an IV.3 cancellation estimate for that piece. -/
theorem wellFactorable_signedError_sq_le_fullLevel_exponential_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M ν : ℝ,
      1 ≤ M → 4 * M * T z = x →
      ε ≤ ν → ν ≤ 1 / 10 → T z = x ^ ν →
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
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
            ∃ b ≤ J, ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
              signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
                24 * M * (∑ m ∈ U, α m ^ 2) * (J + 1 : ℕ) *
                  ‖wExtractedBlockExponential (wUniformCutoff M (x ^ η)) (N z)
                    (Ioc 0 ⌊L⌋₊) (betaClean (β z) a)
                    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                    γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b (M * y)‖ +
                  x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_fullLevel_dyadic_c2
    (i := i) (j := j) A hSW hT hN hβ hε hη] with x hx
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U hU α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha0 hax
  obtain ⟨b, hb, hbound⟩ := ha a ha0 hax
  obtain ⟨y, hy, _, hmax⟩ := wExtractedFrequencyBlock_le_max
    (lt_of_lt_of_le (by norm_num) hM) (wUniformCutoff M (x ^ η))
    (N z) (Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊) (betaClean (β z) a)
    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a
    (c2FiveSmallMask x η) (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε)
    (highOmegaCutoff x) b
  refine ⟨b, hb, y, hy, hbound.trans (add_le_add ?_ le_rfl)⟩
  have hscale := mul_le_mul_of_nonneg_left hmax
    (show 0 ≤ 8 * (∑ m ∈ U, α m ^ 2) *
      (Nat.log 2 ⌈(x ^ ((5 - 5 * ν) / 9 - ε)) ^ 2 / M * x ^ η⌉₊ + 1 : ℕ)
      from by positivity)
  convert hscale using 1
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
