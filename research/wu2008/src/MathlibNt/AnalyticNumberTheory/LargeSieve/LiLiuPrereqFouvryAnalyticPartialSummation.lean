import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryRectangleSlowVariation

/-!
# Concrete slow-weight removal from the actual extracted dispersion sum

The degree-five variation loss is derived from actual floor-retained tuples.
Empty blocks are treated separately. All arithmetic coefficients, phases,
support conditions and the coupled cutoff remain inside genuine prefixes.
-/

noncomputable section
open Classical Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open _root_.LiLiuPrereqFouvry

def wAnalyticVariationConstant (Z : ℝ) : ℝ :=
  2048 * (6 + 2 * Real.pi) ^ 5 * (1 + 112 * Z) ^ 5

theorem wAnalyticVariationConstant_nonneg {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ wAnalyticVariationConstant Z := by
  unfold wAnalyticVariationConstant
  positivity

theorem wAnalyticGridWeight_variation_bound
    {M T x Z y : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive) :
    Rectangle.variation (wAnalyticBoxLo j) (wAnalyticBoxHi j)
      (wAnalyticGridWeight K j positive a (M * y)) ≤ wAnalyticVariationConstant Z := by
  exact Rectangle.variation_normalizedWeight_div_le_all _ _ _
    (wAnalyticDyadicBlock_parameter_budget hM hT hZ hx hy hN hQ ha ht)
    (wAnalyticBoxLo j) (wAnalyticBoxHi j) (fun i => (2 : ℝ) ^ j i)
    (fun _ => by positivity)
    (fun i => by simp [wAnalyticBoxLo])
    (fun i => by simp [wAnalyticBoxHi])

theorem wAnalyticDyadicWeightedBlock_norm_le_prefix
    {M T x Z y : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ x)
    (β c₁ γ ζ : ℕ → ℝ) (P : WOriginalTuple → Prop) (R S ξ : ℝ)
    (b : ℕ) (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool) :
    let U := wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K
    ‖wAnalyticDyadicWeightedBlock U K j positive β c₁ γ ζ a (M * y)‖ ≤
      wBlockAmplitude K j * wAnalyticVariationConstant Z *
        wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j positive) j β c₁ γ ζ a := by
  dsimp only
  have hNp : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (lt_of_lt_of_le hT (hN n hn))
  have hA : 0 ≤ wBlockAmplitude K j := by unfold wBlockAmplitude; positivity
  have hC := wAnalyticVariationConstant_nonneg hZ
  have hP := wAnalyticBlockPrefixMax_nonneg
    (wAnalyticDyadicBlock (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K)
      j positive) j β c₁ γ ζ a
  by_cases hn : (wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive).Nonempty
  · obtain ⟨t, ht⟩ := hn
    have hv := wAnalyticGridWeight_variation_bound hM hT hZ hx hy hN hQ ha ht
    exact (wAnalyticDyadicWeightedBlock_norm_le_variation hNp hQ
      (wFloorCutoff M Z) β c₁ γ ζ a P R S ξ b K j positive (M * y)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hA) hP)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [wAnalyticDyadicWeightedBlock, he, sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg hA hC)
      (wAnalyticBlockPrefixMax_nonneg ∅ j β c₁ γ ζ a)

/-- An explicitly constructed arithmetic quantity: dyadic reciprocal
prefactors times attained, genuinely rectangular arithmetic prefix maxima. -/
def wAnalyticKeyPrefixMajorant (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ j ∈ U.image wAnalyticDyadicKey, wBlockAmplitude K j *
    (wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j true) j β c₁ γ ζ a +
      wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j false) j β c₁ γ ζ a)

theorem wAnalyticKeyPrefixMajorant_nonneg (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    0 ≤ wAnalyticKeyPrefixMajorant U K β c₁ γ ζ a := by
  apply sum_nonneg
  intro j _
  exact mul_nonneg (by unfold wBlockAmplitude; positivity)
    (add_nonneg (wAnalyticBlockPrefixMax_nonneg _ _ _ _ _ _ _)
      (wAnalyticBlockPrefixMax_nonneg _ _ _ _ _ _ _))

/-- The full actual fixed-key exponential sum has now lost its slow weight
at a proved polynomial cost, with no assumed derivative or variation bound. -/
theorem wExtractedFloorKeyExponential_norm_le_prefixes
    {M T x Z y : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ x)
    (β c₁ γ ζ : ℕ → ℝ) (P : WOriginalTuple → Prop) (R S ξ : ℝ)
    (b : ℕ) (K : WExtractedKey) :
    ‖wExtractedKeyExponential (wFloorCutoff M Z) N Q β c₁ γ ζ a P R S ξ b K
      (M * y)‖ ≤
      wAnalyticVariationConstant Z *
        wAnalyticKeyPrefixMajorant
          (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K)
          K β c₁ γ ζ a := by
  have hNp : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (lt_of_lt_of_le hT (hN n hn))
  rw [wExtractedKeyExponential_eq_dyadicWeightedBlocks hNp hQ]
  unfold wAnalyticKeyPrefixMajorant
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j _
  apply (norm_add_le _ _).trans
  have hp := wAnalyticDyadicWeightedBlock_norm_le_prefix hM hT hZ hx hy hN hQ ha
    β c₁ γ ζ P R S ξ b K j true
  have hn := wAnalyticDyadicWeightedBlock_norm_le_prefix hM hT hZ hx hy hN hQ ha
    β c₁ γ ζ P R S ξ b K j false
  exact (add_le_add hp hn).trans (by ring_nf; rfl)

/-- Original signed distribution error after concrete five-variable partial
summation. The Fourier integration point has disappeared; the remaining
maxima contain only the exact arithmetic coefficients and phases. -/
theorem wellFactorable_signedError_sq_le_floor_prefix_c2
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
            ∃ b ≤ J, ∃ K ∈ wExtractedKeyBox (x ^ η),
              signedError U (N z) (Ioc 0 ⌊L⌋₊) α (β z) c a ^ 2 ≤
                3072 * M * (∑ m ∈ U, α m ^ 2) * (J + 1 : ℕ) * (x ^ η) ^ 7 *
                  wAnalyticVariationConstant (x ^ η) *
                  wAnalyticKeyPrefixMajorant
                    (wExtractedKeyFiber (wFloorCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b K)
                    K (betaClean (β z) a)
                    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a +
                  x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_floor_key_c2
    (i := i) (j := j) A hSW hT hN hβ hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U hU α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha0 hax
  obtain ⟨b, hb, y, hy, K, hK, hk⟩ := ha a ha0 hax
  have hZ : 0 ≤ x ^ η := Real.rpow_nonneg (by linarith) η
  have hp := wExtractedFloorKeyExponential_norm_le_prefixes
    (Q := Ioc 0 ⌊x ^ ((5 - 5 * ν) / 9 - ε)⌋₊)
    (lt_of_lt_of_le zero_lt_one hM) (lt_of_lt_of_le zero_lt_one (hT z)) hZ
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
