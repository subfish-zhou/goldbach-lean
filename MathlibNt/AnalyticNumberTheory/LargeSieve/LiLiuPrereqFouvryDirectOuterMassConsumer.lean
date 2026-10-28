import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectOuterMass

/-! A single signed-WF consumer with its split chosen before the shift and
all subsequent frequency/key/cell/prefix choices. The loss is any prescribed
positive power, rather than an uninstantiated coefficient envelope. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem six_smallPower (C X δ : ℝ) (hX : 0 ≤ X) :
    (C * X ^ (δ / 6)) ^ 6 = C ^ 6 * X ^ δ := by
  rw [mul_pow, ← Real.rpow_mul_natCast hX]
  congr 1
  congr 1
  ring


/-- The same arbitrary small power pays the literal outer L2 mass. -/
theorem direct_outerMass_subpower (k m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
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
      wCorrelationOuterMass x N S U c K (betaClean β a)
        (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ≤
          C * X ^ δ * (8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T) := by
  obtain ⟨A, hA, hm⟩ := direct_outerMass_fixedOrder k m (show 0 < δ / 6 by positivity)
  refine ⟨A ^ 6, by positivity, ?_⟩
  intro X hX H N Q a x η R S T b K j positive U c β γ ζ
    hN hQ hNX hQX hR hS hRX hSX hT hNT hβ hγ hζ hU
  simpa only [six_smallPower A X δ (by linarith)] using
    hm X hX H N Q a x η R S T b K j positive U c β γ ζ
      hN hQ hNX hQX hR hS hRX hSX hT hNT hβ hγ hζ hU

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
