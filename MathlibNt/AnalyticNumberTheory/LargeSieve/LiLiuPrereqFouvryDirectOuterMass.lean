import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectCoefficientsSupport

/-! The occupied outer image costs K1*r*T, not H*K1*r*T or K1*r*T².
Every carrier below is the existing coprime fiber of an actual dyadic subset. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A bound on the image, not on the frequency-tuples projecting onto it. -/
theorem direct_outer_image_card
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S T : ℝ} {b : ℕ} {K : WExtractedKey}
    {j : Fin 5 → ℕ} {positive : Bool} {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
        R S (highOmegaCutoff x) b K) j positive)
    (hT : 0 ≤ T) (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2 * T)
    (c : Finset (ℕ × ℕ)) :
    (((wCoprimeFiber x N S U c).image wCorrelationOuter).card : ℝ) ≤
      8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T := by
  let O := (Ioc 0 (2 * 2 ^ j 1)) ×ˢ
    ((Ioc 0 (2 * 2 ^ j 3)) ×ˢ (Ioc 0 ⌊2 * T⌋₊))
  have hsub : (wCoprimeFiber x N S U c).image wCorrelationOuter ⊆ O := by
    intro o ho
    obtain ⟨t, ht, rfl⟩ := mem_image.mp ho
    have hblock := hU (mem_filter.mp ht).1
    have hkey := (mem_filter.mp hblock).1
    have hk := wAnalyticDyadicBlock_bounds hN hQ hblock 1
    have hr := wAnalyticDyadicBlock_bounds hN hQ hblock 3
    have hp := wExtractedKeyFiber_positive hN hQ hkey
    have hn := direct_outer_n_le hN hQ hkey hNT
    have hk' : (wCorrelationOuter t).1 ≤ 2 * 2 ^ j 1 := by
      exact_mod_cast hk.2.le
    have hr' : (wCorrelationOuter t).2.1 ≤ 2 * 2 ^ j 3 := by
      exact_mod_cast hr.2.le
    exact mem_product.mpr ⟨mem_Ioc.mpr ⟨hp.2.2.2.2.1, hk'⟩,
      mem_product.mpr ⟨mem_Ioc.mpr ⟨hp.2.2.2.2.2.2.1, hr'⟩,
        mem_Ioc.mpr ⟨hn.1, Nat.le_floor hn.2⟩⟩⟩
  have hcard : (((wCoprimeFiber x N S U c).image wCorrelationOuter).card : ℝ) ≤
      (O.card : ℝ) := by exact_mod_cast card_le_card hsub
  have hO : (O.card : ℝ) =
      (2 * (2 : ℝ) ^ j 1) * ((2 * (2 : ℝ) ^ j 3) * (⌊2 * T⌋₊ : ℝ)) := by
    simp [O, card_product, Nat.card_Ioc, Nat.cast_mul, Nat.cast_pow]
  rw [hO] at hcard
  calc
    _ ≤ _ := hcard
    _ ≤ (2 * (2 : ℝ) ^ j 1) * ((2 * (2 : ℝ) ^ j 3) * (2 * T)) := by
      gcongr
      exact Nat.floor_le (by positivity)
    _ = _ := by ring

/-- Fixed-order payment on the literal outer image of the original carrier. -/
theorem direct_outerMass_fixedOrder (k m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
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
          (C * X ^ δ) ^ 6 * (8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T) := by
  obtain ⟨C, hC, hw⟩ := direct_actual_weights k m hδ
  refine ⟨C, hC, ?_⟩
  intro X hX H N Q a x η R S T b K j positive U c β γ ζ
    hN hQ hNX hQX hR hS hRX hSX hT hNT hβ hγ hζ hU
  have hweight : ∀ o ∈ (wCoprimeFiber x N S U c).image wCorrelationOuter,
      wCorrelationOuterWeight K (betaClean β a)
        (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ o ^ 2 ≤
          (C * X ^ δ) ^ 6 := by
    intro o ho
    obtain ⟨t, ht, rfl⟩ := mem_image.mp ho
    have hkey := (mem_filter.mp (hU (mem_filter.mp ht).1)).1
    have hb := (hw X hX H N Q a (c2FiveSmallMask x η) R S (highOmegaCutoff x)
      b K β γ ζ hN hQ hNX hQX hR hS hRX hSX hβ hγ hζ t hkey).2
    calc
      _ = |wCorrelationOuterWeight K (betaClean β a)
          (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ
            (wCorrelationOuter t)| ^ 2 := (sq_abs _).symm
      _ ≤ ((C * X ^ δ) ^ 3) ^ 2 := by gcongr
      _ = _ := by ring
  have hm : wCorrelationOuterMass x N S U c K (betaClean β a)
      (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ≤
        (((wCoprimeFiber x N S U c).image wCorrelationOuter).card : ℝ) *
          (C * X ^ δ) ^ 6 := by
    simpa only [wCorrelationOuterMass, nsmul_eq_mul] using
      sum_le_card_nsmul _ _ _ hweight
  calc
    _ ≤ _ := hm
    _ ≤ (8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T) * (C * X ^ δ) ^ 6 :=
      mul_le_mul_of_nonneg_right (direct_outer_image_card hN hQ hU hT hNT c)
        (by positivity)
    _ = _ := mul_comm _ _

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
