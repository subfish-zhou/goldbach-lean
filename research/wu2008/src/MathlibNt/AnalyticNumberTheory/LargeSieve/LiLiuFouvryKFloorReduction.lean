import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKExtracted
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryEffectiveAnalytic
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem wellFactorable_signedError_sq_le_floor_extracted_kscale
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
      R₀ * S₀ = L ∧
        ∃ γ ζ : ℕ → ℝ,
          factorSupported R₀ γ ∧ factorSupported S₀ ζ ∧
          (∀ r, |γ r| ≤ (fouvryTau j r : ℝ)) ∧
          (∀ s, |ζ s| ≤ (fouvryTau j s : ℝ)) ∧ c = factorConvolution γ ζ ∧
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
            signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
              8 * (∑ m ∈ U, α m ^ 2) *
                wMaskedFactorExtractedTruncated M (wFloorCutoff M (x ^ η)) (N z)
                  (Ioc 0 ⌊L⌋₊) (betaClean (β z) a)
                  (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                  γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) +
                x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    wellFactorable_signedError_sq_le_five_small_extracted_kscale
      (i := i) (j := j) (A + 2) hSW hT hN hβ hCscale hε hη,
    wMaskedTruncated_ceil_sub_floor_alpha_log_payment i k (j + j) (A + 2) hη,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ)]
    with x hentry hdiff hx hlog
  intro z M ν hM hscale hεν hν hpower U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγs, hζs, hγ, hζ, hec, he⟩ :=
    hentry z M ν hM hscale hεν hν hpower U
      (Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊) hU (Subset.refl _) α c hα hc
  refine ⟨hRS, γ, ζ, hγs, hζs, hγ, hζ, hec, ?_⟩
  intro a ha hax
  have hM0 : 0 < M := by linarith
  have hMx : 2 * M ≤ x := by nlinarith [hT z]
  have hTx : 2 * T z ≤ x := by nlinarith [hT z]
  have hLx : x ^ ((5 - 5 * ν) / 9 - ε) ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx
        (show (5 - 5 * ν) / 9 - ε ≤ 1 by linarith)
  have hUx : U ⊆ Ioc 0 ⌊x⌋₊ := by
    intro m hm
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor ((hU m hm).2.trans hMx)⟩
    have hp : (0 : ℝ) < m := by have := (hU m hm).1; linarith
    exact_mod_cast hp
  have hNx : N z ⊆ Ioc 0 ⌊x⌋₊ := by
    intro n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor ((hN z n hn).2.trans hTx)⟩
    have hp : (0 : ℝ) < n := by have := (hN z n hn).1; have := hT z; linarith
    exact_mod_cast hp
  have hQx : Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊ ⊆ Ioc 0 ⌊x⌋₊ :=
    Ioc_subset_Ioc_right (Nat.floor_mono hLx)
  have hclean : ∀ n ∈ N z, |betaClean (β z) a n| ≤ (fouvryTau k n : ℝ) :=
    fun n hn => (abs_betaClean_le _ _ _).trans (hβ z n hn)
  have hweight : ∀ q, |factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)) q| ≤
      (fouvryTau (j + j) q : ℝ) :=
    factorConvolution_abs_le j j γ _ hγ
      (fun s => (abs_betaLowOmega_le ζ (highOmegaCutoff x) s).trans (hζ s))
  have hd := hdiff M hM0 U (N z)
    (Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊) hUx hNx hQx α
    (betaClean (β z) a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
    hα hclean (fun q _ => hweight q) a (c2FiveSmallMask x η)
  rw [wMaskedTruncated_eq_factorExtracted_of_eq hγs hζs rfl,
    wMaskedTruncated_eq_factorExtracted_of_eq hγs hζs rfl] at hd
  have hα0 : 0 ≤ ∑ m ∈ U, α m ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hd' := (mul_le_mul_of_nonneg_left (le_abs_self _) hα0).trans hd
  have hpay : 9 * (x ^ 2 / Real.log x ^ (A + 2)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_add, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log x))).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (show 0 ≤ Real.log x ^ 2 - 9 by nlinarith)]
  have he' := he a ha hax
  nlinarith

/-- The corrected original-error endpoint with the same explicit six-key
and shell costs. The selected fiber has a genuinely bounded Fourier scale. -/
theorem wellFactorable_signedError_sq_le_floor_key_kscale
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
            ∃ b ≤ J, ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
              ∃ K ∈ wExtractedKeyBox (x ^ η),
                signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
                  3072 * M * (∑ m ∈ U, α m ^ 2) * (J + 1 : ℕ) * (x ^ η) ^ 7 *
                    ‖wExtractedKeyExponential (wFloorCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) (betaClean (β z) a)
                      (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                      γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b K (M * y)‖ +
                    x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_floor_extracted_kscale
    (i := i) (j := j) A hSW hT hN hβ hCscale hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U hU α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha0 hax
  obtain ⟨b, hb, y, hy, K, hK, hk⟩ := wMaskedFactorExtractedTruncated_key_bound_of_cutoff_le
    (lt_of_lt_of_le zero_lt_one hM) (Real.rpow_nonneg (by linarith) η)
    (Real.rpow_nonneg (by linarith : 0 ≤ x) ((5 - 5 * ν) / 9 - ε))
    (wFloorCutoff M (x ^ η)) (fun q _ r _ => wFloorCutoff_le_uniformCutoff M (x ^ η) q r)
    (N z) (betaClean (β z) a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
    γ ζ a x η (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε)
    (highOmegaCutoff x) (Real.one_le_rpow hx1 hη.le)
  refine ⟨b, hb, y, hy, K, hK, (ha a ha0 hax).trans (add_le_add ?_ le_rfl)⟩
  have hb' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hk)
    (show 0 ≤ 8 * (∑ m ∈ U, α m ^ 2) from by positivity)
  convert hb' using 1
  ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
