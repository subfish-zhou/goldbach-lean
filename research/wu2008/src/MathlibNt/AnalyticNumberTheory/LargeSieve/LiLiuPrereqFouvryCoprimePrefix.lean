import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryActualCoprimePartition
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPartialSummation

/-!
# The actual coprimality partition back at the original distribution error

Only the triangle inequality between Lemma 7 cells is used. Every cell
contains the original signed coefficients, tuple multiplicities, arithmetic
phases and remaining filters. This is not an unweighted Weil estimate.
-/

noncomputable section
open Classical Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wAnalyticPrefixSum_eq_coprimeFibers
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (B : Finset (WExtractedTuple × ℤ))
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (cap : Fin 5 → ℕ) :
    wAnalyticPrefixSum B β c₁ γ ζ a cap =
      ∑ c ∈ B.image (wCoprimeLabel x N S),
        wAnalyticPrefixSum (wCoprimeFiber x N S B c) β c₁ γ ζ a cap := by
  have he := sum_fiberwise_of_maps_to
    (s := wAnalyticPrefix B cap) (t := B.image (wCoprimeLabel x N S))
    (g := wCoprimeLabel x N S)
    (fun t ht => mem_image.mpr ⟨t, (mem_filter.mp ht).1, rfl⟩)
    (fun t => (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
      wExtractedArithmeticPhase a t.2 t.1)
  unfold wAnalyticPrefixSum
  rw [← he]
  apply sum_congr rfl
  intro c _
  apply sum_congr
  · ext t
    simp only [wAnalyticPrefix, wCoprimeFiber, mem_filter]
    tauto
  · intro _ _
    rfl

def wCoprimeBlockPrefixMajorant (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (B : Finset (WExtractedTuple × ℤ)) (j : Fin 5 → ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ c ∈ B.image (wCoprimeLabel x N S),
    wAnalyticBlockPrefixMax (wCoprimeFiber x N S B c) j β c₁ γ ζ a

theorem wCoprimeBlockPrefixMajorant_nonneg
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (B : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    0 ≤ wCoprimeBlockPrefixMajorant x N S B j β c₁ γ ζ a :=
  sum_nonneg (fun _ _ => wAnalyticBlockPrefixMax_nonneg _ _ _ _ _ _ _)

/-- The attained prefix is split into genuine coprimality cells. Different
cells may choose different attaining caps, which only increases this bound. -/
theorem wAnalyticBlockPrefixMax_le_coprime
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (B : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    wAnalyticBlockPrefixMax B j β c₁ γ ζ a ≤
      wCoprimeBlockPrefixMajorant x N S B j β c₁ γ ζ a := by
  obtain ⟨cap, hcap, he⟩ := wAnalyticBlockPrefixMax_attained B j β c₁ γ ζ a
  rw [he, wAnalyticPrefixSum_eq_coprimeFibers x N S]
  exact (norm_sum_le _ _).trans
    (sum_le_sum (fun c _ => wAnalyticPrefixSum_norm_le_max
      (wCoprimeFiber x N S B c) j β c₁ γ ζ a cap hcap))

def wCoprimeKeyPrefixMajorant (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (U : Finset (WExtractedTuple × ℤ)) (K : WExtractedKey)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ j ∈ U.image wAnalyticDyadicKey, wBlockAmplitude K j *
    (wCoprimeBlockPrefixMajorant x N S (wAnalyticDyadicBlock U j true) j β c₁ γ ζ a +
      wCoprimeBlockPrefixMajorant x N S (wAnalyticDyadicBlock U j false) j β c₁ γ ζ a)

theorem wAnalyticKeyPrefixMajorant_le_coprime
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    wAnalyticKeyPrefixMajorant U K β c₁ γ ζ a ≤
      wCoprimeKeyPrefixMajorant x N S U K β c₁ γ ζ a := by
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (add_le_add (wAnalyticBlockPrefixMax_le_coprime _ _ _ _ _ _ _ _ _ _)
      (wAnalyticBlockPrefixMax_le_coprime _ _ _ _ _ _ _ _ _ _))
    (by unfold wBlockAmplitude; positivity)

/-- All the arithmetic prefixes used in the new majorant satisfy the
cross-coprimality conclusion proved on the original carrier. -/
theorem wCoprimePrefix_cross_coprime {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {t u : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticPrefix (wCoprimeFiber x N S
      (wAnalyticDyadicBlock (wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
        R S (highOmegaCutoff x) b K) j positive) c) cap)
    (hu : u ∈ wAnalyticPrefix (wCoprimeFiber x N S
      (wAnalyticDyadicBlock (wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
        R S (highOmegaCutoff x) b K) j positive) c) cap) :
    (wCoprimePair t.1).1.Coprime (wCoprimePair u.1).2 ∧
      (wCoprimePair u.1).1.Coprime (wCoprimePair t.1).2 :=
  wCoprimeFiber_cross_coprime hN hQ (fun _ hv => (mem_filter.mp hv).1)
    (mem_filter.mp ht).1 (mem_filter.mp hu).1

/-- Uniform subpolynomial count for the actual C.2 dyadic cells, with no
additional size hypothesis on the product coordinate. -/
theorem eventually_c2_wCoprimeLabel_count {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ x : ℝ in atTop, ∀ (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (a : ℤ)
      (η ν ε : ℝ) (b : ℕ) (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool),
      0 ≤ ε → ε ≤ ν → ν ≤ 1 / 10 →
      (∀ n ∈ N, 0 < n ∧ (n : ℝ) ≤ 2 * x ^ ν) → (∀ q ∈ Q, 0 < q) →
      let S := x ^ c2SExponent ν ε
      let U := wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
        (x ^ c2RExponent ν ε) S (highOmegaCutoff x) b K
      (((wAnalyticDyadicBlock U j positive).image (wCoprimeLabel x N S)).card : ℝ) ≤
        x ^ θ := by
  filter_upwards [eventually_wCoprimeLabel_image_card_le hθ,
    eventually_ge_atTop (4 : ℝ)] with x hx hx₄
  intro H N Q a η ν ε b K j positive hε hεν hν hN hQ
  apply hx H N Q a η (x ^ c2RExponent ν ε) (x ^ c2SExponent ν ε) b K _
    (fun n hn => (hN n hn).1) hQ
    (wCoprimePairBound_c2_le hx₄ hε hεν hν (fun n hn => (hN n hn).2))
  exact fun _ ht => (mem_filter.mp ht).1

/-- The original signed error is now bounded by prefixes in constructed
Lemma 7 cells; all WF/SW quantifiers and the full modulus interval survive. -/
theorem wellFactorable_signedError_sq_le_coprime_prefix_c2
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
                  wCoprimeKeyPrefixMajorant x (N z) S₀
                    (wExtractedKeyFiber (wFloorCutoff M (x ^ η)) (N z)
                      (Ioc 0 ⌊L⌋₊) a (c2FiveSmallMask x η) R₀ S₀ (highOmegaCutoff x) b K)
                    K (betaClean (β z) a)
                    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a +
                  x ^ 2 / Real.log x ^ A := by
  filter_upwards [wellFactorable_signedError_sq_le_floor_prefix_c2
    (i := i) (j := j) A hSW hT hN hβ hε hη,
    eventually_ge_atTop (1 : ℝ)] with x hx hx₁
  intro z M ν hM he hεν hν hTν U hU α c hα hc
  obtain ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ha⟩ :=
    hx z M ν hM he hεν hν hTν U hU α c hα hc
  refine ⟨hRS, γ, ζ, hγ, hζ, hγτ, hζτ, hcγ, ?_⟩
  intro a ha₀ hax
  obtain ⟨b, hb, K, hK, hk⟩ := ha a ha₀ hax
  refine ⟨b, hb, K, hK, hk.trans (add_le_add ?_ le_rfl)⟩
  apply mul_le_mul_of_nonneg_left (wAnalyticKeyPrefixMajorant_le_coprime _ _ _ _ _ _ _ _ _ _)
  have hV := wAnalyticVariationConstant_nonneg
    (Real.rpow_nonneg (by linarith : 0 ≤ x) η)
  positivity

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
