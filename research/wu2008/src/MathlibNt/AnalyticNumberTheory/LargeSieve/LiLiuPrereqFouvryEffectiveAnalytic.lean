import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedScale
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFloorCutoff

/-!
# Reusing the actual analytic reduction with a smaller frequency cutoff

The integral, signed coefficients, full modulus interval, and six-key box
are unchanged. Only the genuinely retained frequency set is made smaller.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wExtractedMaxFrequency_le_of_cutoff_le {M Z L : ℝ}
    (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ q ∈ Ioc 0 ⌊L⌋₊, ∀ r ∈ Ioc 0 ⌊L⌋₊,
      H q r ≤ wUniformCutoff M Z q r)
    (N : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    wExtractedMaxFrequency H N (Ioc 0 ⌊L⌋₊) a P R S ξ ≤
      ⌈L ^ 2 / M * Z⌉₊ := by
  unfold wExtractedMaxFrequency
  apply Finset.sup_le
  intro z hz
  obtain ⟨hq, hr⟩ := wExtractedOriginal_reducedModuli hz
  exact (hH _ (mem_filter.mp hq).1 _ (mem_filter.mp hr).1).trans
    (wUniformCutoff_le_fullLevel hM hZ hL
      (mem_filter.mp hq).1 (mem_filter.mp hr).1)

/-- A smaller cutoff uses the same explicit shell count and key loss.
This reuses the proved integral and grouping, without replacing a masked
sum by an unweighted interval. -/
theorem wMaskedFactorExtractedTruncated_key_bound_of_cutoff_le
    {M Z L : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ q ∈ Ioc 0 ⌊L⌋₊, ∀ r ∈ Ioc 0 ⌊L⌋₊,
      H q r ≤ wUniformCutoff M Z q r)
    (N : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (x η R S ξ : ℝ) (hY : 1 ≤ x ^ η) :
    ∃ b ≤ Nat.log 2 ⌈L ^ 2 / M * Z⌉₊, ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
      ∃ K ∈ wExtractedKeyBox (x ^ η),
        |wMaskedFactorExtractedTruncated M H N (Ioc 0 ⌊L⌋₊)
          β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ| ≤
          384 * M * (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) * (x ^ η) ^ 7 *
            ‖wExtractedKeyExponential H N (Ioc 0 ⌊L⌋₊)
              β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K (M * y)‖ := by
  obtain ⟨b, hb, hw⟩ := wMaskedFactorExtractedTruncated_dyadic_bound
    M H N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ
  have hlog := Nat.log_mono_right (b := 2)
    (wExtractedMaxFrequency_le_of_cutoff_le hM hZ hL H hH N a
      (c2FiveSmallMask x η) R S ξ)
  obtain ⟨y, hy, _, hyb⟩ := wExtractedFrequencyBlock_le_max
    hM H N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b
  obtain ⟨K, hK, hKb⟩ := wExtractedBlockExponential_le_keyMax_power
    H N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a x η R S ξ b (M * y) hY
  refine ⟨b, hb.trans hlog, y, hy, K, hK, hw.trans ?_⟩
  calc
    _ ≤ (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
        (3 * M * ‖wExtractedBlockExponential H N (Ioc 0 ⌊L⌋₊)
          β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b (M * y)‖) := by
      apply mul_le_mul _ hyb (norm_nonneg _) (Nat.cast_nonneg _)
      exact_mod_cast Nat.add_le_add_right hlog 1
    _ ≤ (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
        (3 * M * (128 * (x ^ η) ^ 7 *
          ‖wExtractedKeyExponential H N (Ioc 0 ⌊L⌋₊)
            β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K (M * y)‖)) := by
      gcongr
    _ = _ := by ring

/-- The cutoff correction is physically paid in the original signed-error
bound before any Fourier integral or maximum is taken. The legitimate
WF factors still precede every choice of the changing residue. -/
theorem wellFactorable_signedError_sq_le_floor_extracted_c2
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
      R₀ * S₀ = L ∧
        ∃ γ ζ : ℕ → ℝ,
          factorSupported R₀ γ ∧ factorSupported S₀ ζ ∧
          (∀ r, |γ r| ≤ (fouvryTau j r : ℝ)) ∧
          (∀ s, |ζ s| ≤ (fouvryTau j s : ℝ)) ∧ c = factorConvolution γ ζ ∧
          ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
            signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
              8 * (∑ m ∈ U, α m ^ 2) *
                wMaskedFactorExtractedTruncated M (wFloorCutoff M (x ^ η)) (N z)
                  (Ioc 0 ⌊L⌋₊) (betaClean (β z) a)
                  (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                  γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) +
                x ^ 2 / Real.log x ^ A := by
  filter_upwards [
    wellFactorable_signedError_sq_le_five_small_extracted_c2
      (i := i) (j := j) (A + 2) hSW hT hN hβ hε hη,
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
theorem wellFactorable_signedError_sq_le_floor_key_c2
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
              ∃ K ∈ wExtractedKeyBox (x ^ η),
                signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
                  3072 * M * (∑ m ∈ U, α m ^ 2) * (J + 1 : ℕ) * (x ^ η) ^ 7 *
                    ‖wExtractedKeyExponential (wFloorCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) (betaClean (β z) a)
                      (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                      γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b K (M * y)‖ +
                    x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_floor_extracted_c2
    (i := i) (j := j) A hSW hT hN hβ hε hη,
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

/-- The two smooth monomials on each actual floor-retained point have a
uniform budget, with no loss depending on the changing residue or moduli. -/
theorem wExtractedFloorKey_phase_budget
    {M T x Z y : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) :
    let v := wGCDTuple (wExtractedOriginal t.1)
    |(t.2 : ℝ)| *
        (|M * y| / ((K.D : ℝ) * v.k₁ * t.1.1.2.1 * t.1.1.2.2) +
          |(a : ℝ)| / ((v.n₁ : ℝ) * v.k₁ * t.1.1.2.1 * t.1.1.2.2 * K.D')) ≤
      7 * Z := by
  have hNpos : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (hT.trans_le (hN n hn))
  have hf := (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1
  obtain ⟨hz, hlo, hhi⟩ := mem_wExtractedFrequencies_iff.mp hf
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  obtain ⟨hv, _⟩ := wExtractedOriginal_valid hNpos hQ hz
  have hmem : (wExtractedOriginal t.1).2.1 ∈ N := hm.2.2.2.2.2.2.2.1
  have hu : |M * y| ≤ 3 * M := by
    rw [abs_of_nonneg (mul_nonneg hM.le (by linarith [hy.1]))]
    nlinarith [hy.2]
  have hb := wAnalytic_phase_budget hv hM.le hT (hN _ hmem) hx ha hu t.2
  have hl : 0 < (wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 := by
    rw [hv.lcm_eq]
    exact Nat.mul_pos (Nat.mul_pos hv.D_pos hv.k₁_pos) hv.k₂_pos
  have hs := wFloorCutoff_mem_Icc_scale hM hZ hl (mem_Icc.mpr ⟨hlo, hhi⟩)
  have hp := hb.trans (show
      7 * M * |(t.2 : ℝ)| /
          ((wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 : ℝ) ≤
        7 * Z from by
      calc
        _ = 7 * (M * |(t.2 : ℝ)| /
          ((wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num))
  have hk := wExtracted_k₂_eq hNpos hQ hz
  have hmods := wExtractedKeyFiber_moduli ht
  simpa only [hk, Nat.cast_mul, mul_assoc, hmods.1, hmods.2] using hp

/-- Empty or cancelling selected fibers are handled before taking positive
source parameters. This applies to the actual floor endpoint above. -/
theorem wExtractedFloorKey_zero_or_positive
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (M Z : ℝ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) (u : ℝ) :
    wExtractedKeyExponential (wFloorCutoff M Z) N Q β c₁ γ ζ a P R S ξ b K u = 0 ∨
      0 < K.D ∧ 0 < K.D' ∧
        ∃ t ∈ wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K,
          wExtractedCoefficient β c₁ γ ζ t.1 ≠ 0 := by
  rcases wExtractedKeyExponential_zero_or_witness
    (wFloorCutoff M Z) N Q β c₁ γ ζ a P R S ξ b K u with he | ⟨t, ht, hc⟩
  · exact Or.inl he
  · have hp := wExtractedKeyFiber_positive hN hQ ht
    exact Or.inr ⟨hp.1, hp.2.1, t, ht, hc⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
