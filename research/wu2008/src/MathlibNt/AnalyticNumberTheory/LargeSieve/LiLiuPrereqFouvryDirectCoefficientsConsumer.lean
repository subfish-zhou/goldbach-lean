import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectOuterMass

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The occupied Gram labels retain the genuine beta/zeta arguments; fixed
orders, not an assumed numerical envelope, pay their four factors. -/
theorem direct_gram_fixedOrder (k m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey) (b : ℕ)
        (V : Finset (WExtractedTuple × ℤ)) (β ζ : ℕ → ℝ),
      (∀ n ∈ N, 0 < n) → (∀ n ∈ N, (n : ℝ) ≤ X) →
      0 ≤ R → 0 ≤ S → S ≤ X → 0 < M → 0 < Z →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ s, |ζ s| ≤ (fouvryTau m s : ℝ)) →
      V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K →
      ∀ L ∈ wGramLabels V,
        |wGramWeight K (betaClean β a) ζ L| ≤ (C * X ^ δ) ^ 4 := by
  obtain ⟨A, hA, hAt⟩ := direct_tau_subpower k hδ
  obtain ⟨B, hB, hBt⟩ := direct_tau_subpower m hδ
  refine ⟨A + B, by positivity, ?_⟩
  intro X hX N a x η R S M Z K b V β ζ hN hNX hR hS hSX hM hZ hβ hζ hV L hL
  have hE : 0 ≤ (A + B) * X ^ δ := by positivity
  have hb : ∀ n ∈ N, |betaClean β a n| ≤ (A + B) * X ^ δ := by
    intro n hn
    apply ((betaClean_abs_le_fouvryTau hβ a n hn).trans (hAt X hX n (hNX n hn))).trans
    gcongr
    linarith
  have hz : ∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ (A + B) * X ^ δ := by
    intro s hs
    have hsX : (s : ℝ) ≤ X :=
      (show (s : ℝ) ≤ ⌊S⌋₊ by exact_mod_cast (mem_Ioc.mp hs).2).trans
        ((Nat.floor_le hS).trans hSX)
    apply ((hζ s).trans (hBt X hX s hsX)).trans
    gcongr
    linarith
  have hbnd := wGramWeight_abs_le_of_support hN hR hS hM hZ hV
    (betaClean β a) ζ hE hE hb hz hL
  convert hbnd using 1
  ring

/-- This consumes the already-proved original prefix Cauchy theorem. The
only remaining energy is the existing genuine separated energy, not a new
abstract input or an unweighted interval replacement. -/
theorem direct_prefix_fixedOrder (k m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (a : ℤ)
        (x η R S T : ℝ) (b : ℕ) (K : WExtractedKey)
        (j : Fin 5 → ℕ) (positive : Bool) (U : Finset (WExtractedTuple × ℤ))
        (c : Finset (ℕ × ℕ)) (β γ ζ : ℕ → ℝ),
      (∀ n ∈ N, 0 < n) → (∀ q ∈ Q, 0 < q) →
      (∀ n ∈ N, (n : ℝ) ≤ X) → (∀ q ∈ Q, (q : ℝ) ≤ X) →
      0 ≤ R → 0 ≤ S → R ≤ X → S ≤ X →
      0 ≤ T → (∀ n ∈ N, (n : ℝ) ≤ 2 * T) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau m n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau m n : ℝ)) →
      U ⊆ wAnalyticDyadicBlock
        (wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
          R S (highOmegaCutoff x) b K) j positive →
      ∃ cap ∈ _root_.LiLiuPrereqFouvry.Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j),
        wAnalyticBlockPrefixMax (wCoprimeFiber x N S U c) j (betaClean β a)
          (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a ^ 2 ≤
          ((C * X ^ δ) ^ 6 * (8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T)) *
            wSeparatedCorrelationEnergy x N S (wAnalyticPrefix U cap) c K
              (betaClean β a) ζ a := by
  obtain ⟨C, hC, hm⟩ := direct_outerMass_fixedOrder k m hδ
  refine ⟨C, hC, ?_⟩
  intro X hX H N Q a x η R S T b K j positive U c β γ ζ
    hN hQ hNX hQX hR hS hRX hSX hT hNT hβ hγ hζ hU
  have hkey : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K := fun _ ht => (mem_filter.mp (hU ht)).1
  obtain ⟨cap, hcap, hp⟩ := wCoprimePrefixMax_sq_le_separated_correlation hN hQ hkey
    c j (betaClean β a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ
  refine ⟨cap, hcap, hp.trans ?_⟩
  apply mul_le_mul_of_nonneg_right
  · exact hm X hX H N Q a x η R S T b K j positive (wAnalyticPrefix U cap)
      c β γ ζ hN hQ hNX hQX hR hS hRX hSX hT hNT hβ hγ hζ
        (fun _ ht => hU (mem_filter.mp ht).1)
  · exact wSeparatedCorrelationEnergy_nonneg hN hQ
      (fun _ ht => hkey (mem_filter.mp ht).1) c (betaClean β a) ζ

/-- Legal WF splitting supplies exactly the factor hypotheses used above.
The split precedes the signed shift, cutoffs and all occupied Gram carriers. -/
theorem direct_wellFactorable_envelopes (k m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (N : Finset ℕ) (β c₀ : ℕ → ℝ) (L R S : ℝ),
      (∀ n ∈ N, (n : ℝ) ≤ X) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      SignedWellFactorable m L c₀ → 1 ≤ R → 1 ≤ S → R * S = L →
      ∃ γ ζ : ℕ → ℝ,
        factorSupported R γ ∧ factorSupported S ζ ∧
        (∀ n, |γ n| ≤ (fouvryTau m n : ℝ)) ∧
        (∀ n, |ζ n| ≤ (fouvryTau m n : ℝ)) ∧ c₀ = factorConvolution γ ζ ∧
        ∀ (a : ℤ) (ξ : ℝ),
          (∀ n ∈ N, |betaClean β a n| ≤ C * X ^ δ) ∧
          (∀ n : ℕ, (n : ℝ) ≤ X → |γ n| ≤ C * X ^ δ) ∧
          (∀ n : ℕ, (n : ℝ) ≤ X → |ζ n| ≤ C * X ^ δ) ∧
          (∀ n : ℕ, (n : ℝ) ≤ X →
            |factorConvolution γ (betaLowOmega ζ ξ) n| ≤ C * X ^ δ) := by
  obtain ⟨C, hC, he⟩ := direct_fixedOrder_envelopes k m hδ
  refine ⟨C, hC, ?_⟩
  intro X hX N β c₀ L R S hNX hβ hc hR hS hRS
  obtain ⟨γ, ζ, hg, hz, hgτ, hzτ, heq⟩ := hc.2 R S hR hS hRS
  exact ⟨γ, ζ, hg, hz, hgτ, hzτ, heq,
    fun a ξ => he X hX N β γ ζ a ξ hNX hβ hgτ hzτ⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
