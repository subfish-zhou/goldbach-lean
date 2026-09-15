import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedAnalyticReduction

/-!
# Quantitative six-key grouping of the actual extracted exponential sum

The five canonical gcd coordinates and the extraction divisor `Δ` give an
explicit finite box. The complementary divisor `Δ'` is determined on each
fiber. All original masks, cutoffs, signed coefficients, and both frequency
signs remain in the actual fiber sums. The triangle inequality is used only
between these fibers, not between their oscillatory summands.

This supplies the finite-key cost underlying Fouvry (1987), p. 627, (3.12).
It is not an IV.3 cancellation estimate or a completion of C.2.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WExtractedKey := (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ

def wExtractedKey (z : WExtractedTuple) : WExtractedKey :=
  ((wGCDTuple (wExtractedOriginal z)).key, z.1.1.1)

/-- A full rectangular box, not the image of the actual carrier. -/
def wExtractedKeyBox (Y : ℝ) : Finset WExtractedKey :=
  (range (⌊Y⌋₊ + 1) ×ˢ
    (range (⌊Y⌋₊ + 1) ×ˢ
      (range (⌊Y⌋₊ + 1) ×ˢ
        (range (⌊Y⌋₊ + 1) ×ˢ range (⌊Y⌋₊ + 1))))) ×ˢ
    range (⌊Y ^ 2⌋₊ + 1)

theorem mem_wExtractedKeyBox_iff {Y : ℝ} {K : WExtractedKey} :
    K ∈ wExtractedKeyBox Y ↔
      K.1.1 ≤ ⌊Y⌋₊ ∧ K.1.2.1 ≤ ⌊Y⌋₊ ∧ K.1.2.2.1 ≤ ⌊Y⌋₊ ∧
      K.1.2.2.2.1 ≤ ⌊Y⌋₊ ∧ K.1.2.2.2.2 ≤ ⌊Y⌋₊ ∧ K.2 ≤ ⌊Y ^ 2⌋₊ := by
  simp [wExtractedKeyBox, and_assoc]

theorem wExtractedKeyBox_nonempty (Y : ℝ) : (wExtractedKeyBox Y).Nonempty :=
  ⟨((0, 0, 0, 0, 0), 0), mem_wExtractedKeyBox_iff.mpr
    ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩⟩

theorem wExtractedKeyBox_card (Y : ℝ) :
    (wExtractedKeyBox Y).card = (⌊Y⌋₊ + 1) ^ 5 * (⌊Y ^ 2⌋₊ + 1) := by
  simp only [wExtractedKeyBox, card_product, card_range]
  ring

theorem wExtractedKeyBox_card_le {Y : ℝ} (hY : 1 ≤ Y) :
    ((wExtractedKeyBox Y).card : ℝ) ≤ 128 * Y ^ 7 := by
  have hY0 : 0 ≤ Y := by linarith
  have hY2 : 1 ≤ Y ^ 2 := by nlinarith
  have hA : (⌊Y⌋₊ : ℝ) + 1 ≤ 2 * Y := by
    linarith [Nat.floor_le hY0]
  have hB : (⌊Y ^ 2⌋₊ : ℝ) + 1 ≤ 2 * Y ^ 2 := by
    linarith [Nat.floor_le (sq_nonneg Y)]
  rw [wExtractedKeyBox_card]
  push_cast
  calc
    _ ≤ (2 * Y) ^ 5 * (2 * Y ^ 2) := by gcongr
    _ = 64 * Y ^ 7 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hY0 7)

/-- The actual extraction equation and strict positivity, without replacing
`Δ'` by a new independent coordinate. -/
theorem wExtracted_extraction_spec {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {z : WExtractedTuple}
    (hz : z ∈ wFactorExtractionTuples N Q a P R S ξ) :
    0 < z.1.1.1 ∧ 0 < z.1.1.2 ∧
      z.1.1.1 * z.1.1.2 =
        (wGCDTuple (wExtractedOriginal z)).δ * (wGCDTuple (wExtractedOriginal z)).δ₂ ∧
      P (wExtractedOriginal z) := by
  obtain ⟨hD, hD', _, _, _, _, _, _, _, _, _, hP, _, he, _⟩ :=
    mem_wFactorExtractionTuples_iff.mp hz
  exact ⟨(mem_Ioc.mp hD).1, (mem_Ioc.mp hD').1, he.symm, hP⟩

/-- Membership of the full six-key box follows from the actual mask and
the extraction equation; `Δ ≤ δ*δ₂ ≤ Y²` uses `Δ' > 0`. -/
theorem wExtractedKey_mem_box {N Q : Finset ℕ} {a : ℤ}
    {x η R S ξ : ℝ} {z : WExtractedTuple}
    (hz : z ∈ wFactorExtractionTuples N Q a (c2FiveSmallMask x η) R S ξ) :
    wExtractedKey z ∈ wExtractedKeyBox (x ^ η) := by
  obtain ⟨_, hD', he, hP⟩ := wExtracted_extraction_spec hz
  have hd : ((wGCDTuple (wExtractedOriginal z)).d : ℝ) ≤ x ^ η := hP.1.1.1.1
  have hd₁ : ((wGCDTuple (wExtractedOriginal z)).d₁ : ℝ) ≤ x ^ η := hP.1.2
  have hδ : ((wGCDTuple (wExtractedOriginal z)).δ : ℝ) ≤ x ^ η := hP.1.1.2
  have hδ₁ : ((wGCDTuple (wExtractedOriginal z)).δ₁ : ℝ) ≤ x ^ η := hP.2.1
  have hδ₂ : ((wGCDTuple (wExtractedOriginal z)).δ₂ : ℝ) ≤ x ^ η := hP.2.2
  have hY0 : 0 ≤ x ^ η := (Nat.cast_nonneg _).trans hδ
  have hD : (z.1.1.1 : ℝ) ≤ (x ^ η) ^ 2 := by
    have hn : z.1.1.1 ≤ z.1.1.1 * z.1.1.2 := by nlinarith
    have hp : (z.1.1.1 : ℝ) ≤
        (wGCDTuple (wExtractedOriginal z)).δ * (wGCDTuple (wExtractedOriginal z)).δ₂ := by
      exact_mod_cast hn.trans_eq he
    exact hp.trans (by nlinarith [mul_le_mul hδ hδ₂ (Nat.cast_nonneg _) hY0])
  exact mem_wExtractedKeyBox_iff.mpr
    ⟨Nat.le_floor hd, Nat.le_floor hd₁, Nat.le_floor hδ,
      Nat.le_floor hδ₁, Nat.le_floor hδ₂, Nat.le_floor hD⟩

/-- The carrier remains a filter of the original extracted frequency block. -/
def wExtractedKeyFiber (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) :
    Finset (WExtractedTuple × ℤ) :=
  (frequencyBlock (wExtractedFrequencies H N Q a P R S ξ) Prod.snd b).filter
    (fun t ↦ wExtractedKey t.1 = K)

theorem mem_wExtractedKeyFiber_iff {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ} :
    t ∈ wExtractedKeyFiber H N Q a P R S ξ b K ↔
      t ∈ frequencyBlock (wExtractedFrequencies H N Q a P R S ξ) Prod.snd b ∧
        wExtractedKey t.1 = K := by
  simp only [wExtractedKeyFiber, mem_filter]

/-- Fixed canonical source data on a fiber, including the determined
complementary extraction divisor. -/
theorem wExtractedKeyFiber_spec {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    (wGCDTuple (wExtractedOriginal t.1)).key = K.1 ∧
      t.1.1.1.1 = K.2 ∧ 0 < K.2 ∧ 0 < t.1.1.1.2 ∧
      t.1.1.1.2 = K.1.2.2.1 * K.1.2.2.2.2 / K.2 := by
  obtain ⟨ht, hk⟩ := mem_wExtractedKeyFiber_iff.mp ht
  have hz := (mem_wExtractedFrequencies_iff.mp (mem_filter.mp ht).1).1
  obtain ⟨hD, hD', he, _⟩ := wExtracted_extraction_spec hz
  have hk₁ := congrArg Prod.fst hk
  have hk₂ := congrArg Prod.snd hk
  change (wGCDTuple (wExtractedOriginal t.1)).key = K.1 at hk₁
  change t.1.1.1.1 = K.2 at hk₂
  refine ⟨hk₁, hk₂, hk₂ ▸ hD, hD', ?_⟩
  rw [← hk₁, ← hk₂]
  change t.1.1.1.2 =
    ((wGCDTuple (wExtractedOriginal t.1)).δ *
      (wGCDTuple (wExtractedOriginal t.1)).δ₂) / t.1.1.1.1
  rw [← he, Nat.mul_div_cancel_left _ hD]

def wExtractedKeyExponential (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop)
    (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) (u : ℝ) : ℂ :=
  wFourierExponentialSum (wExtractedKeyFiber H N Q a P R S ξ b K)
    (fun t ↦ wExtractedCoefficient β c₁ γ ζ t.1) a
    (fun t ↦ (wExtractedOriginal t.1).1.1)
    (fun t ↦ (wExtractedOriginal t.1).1.2)
    (fun t ↦ (wExtractedOriginal t.1).2.1)
    (fun t ↦ (wExtractedOriginal t.1).2.2) Prod.snd u

theorem wExtractedBlockExponential_eq_sum_keys
    (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ)
    (a : ℤ) (x η R S ξ : ℝ) (b : ℕ) (u : ℝ) :
    wExtractedBlockExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b u =
      ∑ K ∈ wExtractedKeyBox (x ^ η),
        wExtractedKeyExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K u := by
  unfold wExtractedBlockExponential wExtractedKeyExponential wFourierExponentialSum
    wExtractedKeyFiber
  symm
  apply sum_fiberwise_of_maps_to
  intro t ht
  exact wExtractedKey_mem_box
    (mem_wExtractedFrequencies_iff.mp (mem_filter.mp ht).1).1

/-- A key attaining the maximum of the actual fiber sums, with the exact
rectangular-box cardinality as loss. Empty source carriers cause no problem. -/
theorem wExtractedBlockExponential_le_keyMax
    (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ)
    (a : ℤ) (x η R S ξ : ℝ) (b : ℕ) (u : ℝ) :
    ∃ K ∈ wExtractedKeyBox (x ^ η),
      (∀ K' ∈ wExtractedKeyBox (x ^ η),
        ‖wExtractedKeyExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K' u‖ ≤
          ‖wExtractedKeyExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K u‖) ∧
      ‖wExtractedBlockExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b u‖ ≤
        ((wExtractedKeyBox (x ^ η)).card : ℝ) *
          ‖wExtractedKeyExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K u‖ := by
  obtain ⟨K, hK, hmax⟩ := exists_max_image (wExtractedKeyBox (x ^ η))
    (fun K ↦ ‖wExtractedKeyExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K u‖)
    (wExtractedKeyBox_nonempty _)
  refine ⟨K, hK, hmax, ?_⟩
  rw [wExtractedBlockExponential_eq_sum_keys]
  exact (norm_sum_le _ _).trans (by
    simpa only [nsmul_eq_mul] using sum_le_card_nsmul (wExtractedKeyBox (x ^ η))
      (fun K ↦ ‖wExtractedKeyExponential H N Q β c₁ γ ζ a
        (c2FiveSmallMask x η) R S ξ b K u‖) _ hmax)

theorem wExtractedBlockExponential_le_keyMax_power
    (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ)
    (a : ℤ) (x η R S ξ : ℝ) (b : ℕ) (u : ℝ) (hY : 1 ≤ x ^ η) :
    ∃ K ∈ wExtractedKeyBox (x ^ η),
      ‖wExtractedBlockExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b u‖ ≤
        128 * (x ^ η) ^ 7 *
          ‖wExtractedKeyExponential H N Q β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K u‖ := by
  obtain ⟨K, hK, _, hb⟩ := wExtractedBlockExponential_le_keyMax H N Q β c₁ γ ζ a x η R S ξ b u
  exact ⟨K, hK, hb.trans (mul_le_mul_of_nonneg_right
    (wExtractedKeyBox_card_le hY) (norm_nonneg _))⟩

/-- The actual full-level extracted W is bounded by one actual six-key
fiber. The logarithmic shell cost and polynomial key cost are explicit. -/
theorem wMaskedFactorExtractedTruncated_fullLevel_key_bound
    {M Z L : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (N : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (x η R S ξ : ℝ) (hY : 1 ≤ x ^ η) :
    ∃ b ≤ Nat.log 2 ⌈L ^ 2 / M * Z⌉₊, ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
      ∃ K ∈ wExtractedKeyBox (x ^ η),
        |wMaskedFactorExtractedTruncated M (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊)
          β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ| ≤
          384 * M * (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) * (x ^ η) ^ 7 *
            ‖wExtractedKeyExponential (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊)
              β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K (M * y)‖ := by
  obtain ⟨b, hb, y, hy, hw⟩ :=
    wMaskedFactorExtractedTruncated_fullLevel_exponential_bound
      hM hZ hL N β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ
  obtain ⟨K, hK, hk⟩ := wExtractedBlockExponential_le_keyMax_power
    (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a x η R S ξ b (M * y) hY
  refine ⟨b, hb, y, hy, K, hK, hw.trans ?_⟩
  have hscale := mul_le_mul_of_nonneg_left hk
    (show 0 ≤ 3 * M * (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) from by positivity)
  convert hscale using 1
  ring

/-- The original signed-error endpoint with quantitative six-key cost.
WF factors are still chosen before `a`; no new SW hypothesis, arbitrary
fiber bound, or cancellation claim is introduced. -/
theorem wellFactorable_signedError_sq_le_fullLevel_key_c2
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
                    ‖wExtractedKeyExponential (wUniformCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) (betaClean (β z) a)
                      (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
                      γ ζ a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b K (M * y)‖ +
                    x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_fullLevel_exponential_c2
    (i := i) (j := j) A hSW hT hN hβ hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U hU α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha0 hax
  obtain ⟨b, hb, y, hy, hw⟩ := ha a ha0 hax
  obtain ⟨K, hK, hk⟩ := wExtractedBlockExponential_le_keyMax_power
    (wUniformCutoff M (x ^ η)) (N z) (Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊)
    (betaClean (β z) a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x)))
    γ ζ a x η (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε)
    (highOmegaCutoff x) b (M * y) (Real.one_le_rpow hx1 hη.le)
  refine ⟨b, hb, y, hy, K, hK, hw.trans (add_le_add ?_ le_rfl)⟩
  have hscale := mul_le_mul_of_nonneg_left hk
    (show 0 ≤ 24 * M * (∑ m ∈ U, α m ^ 2) *
      (Nat.log 2 ⌈(x ^ ((5 - 5 * ν) / 9 - ε)) ^ 2 / M * x ^ η⌉₊ + 1 : ℕ)
      from by positivity)
  convert hscale using 1
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
