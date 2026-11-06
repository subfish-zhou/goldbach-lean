import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectOuterMass

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry


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


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
