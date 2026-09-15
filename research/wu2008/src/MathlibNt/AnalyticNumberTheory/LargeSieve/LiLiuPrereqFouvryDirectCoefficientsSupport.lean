import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectCoefficients

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All five coefficient arguments are the original support arguments. -/
theorem direct_coefficient_support
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    K.2 * (wCorrelationOuter t).2.1 ∈ Ioc 0 ⌊R⌋₊ ∧
    K.1.2.2.1 * K.1.2.2.2.1 * (wCorrelationOuter t).1 ∈ Q ∧
    K.1.1 * K.1.2.1 * (wCorrelationOuter t).2.2 ∈ N ∧
    (K.1.2.2.1 * K.1.2.2.2.2 / K.2) * t.1.1.2.2 ∈ Ioc 0 ⌊S⌋₊ ∧
    K.1.1 * (wGCDTuple (wExtractedOriginal t.1)).n₂ ∈ N := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  obtain ⟨hD, hD', hr, hs, hRb, hSb, hq, hn₁, hn₂, _⟩ :=
    mem_wFactorExtractionTuples_iff.mp hz
  have hk := (wExtractedKeyFiber_spec ht).1
  have hd := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.1) hk
  have hd₁ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.1) hk
  have hδ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.1) hk
  have hδ₁ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.2.1) hk
  change (wGCDTuple (wExtractedOriginal t.1)).d = K.1.1 at hd
  change (wGCDTuple (wExtractedOriginal t.1)).d₁ = K.1.2.1 at hd₁
  change (wGCDTuple (wExtractedOriginal t.1)).δ = K.1.2.2.1 at hδ
  change (wGCDTuple (wExtractedOriginal t.1)).δ₁ = K.1.2.2.2.1 at hδ₁
  have eqQ := hv.q_eq
  have eqN₁ := hv.N₁_eq
  have eqN₂ := hv.N₂_eq
  rw [hd, hd₁] at eqN₁
  rw [hd] at eqN₂
  rw [hδ, hδ₁] at eqQ
  dsimp only [wCorrelationOuter]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← (wExtractedKeyFiber_spec ht).2.1]
    exact mem_Ioc.mpr ⟨Nat.mul_pos (mem_Ioc.mp hD).1 (mem_Ioc.mp hr).1, hRb⟩
  · rw [← eqQ]
    exact (mem_filter.mp hq).1
  · rw [← eqN₁]
    exact hn₁
  · rw [← (wExtractedKeyFiber_spec ht).2.2.2.2]
    exact mem_Ioc.mpr ⟨Nat.mul_pos (mem_Ioc.mp hD').1 (mem_Ioc.mp hs).1, hSb⟩
  · rw [← eqN₂]
    exact hn₂

/-- One original beta coordinate bounds the shared reduced n1; no second copy. -/
theorem direct_outer_n_le
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ T : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K)
    (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2 * T) :
    0 < (wCorrelationOuter t).2.2 ∧ ((wCorrelationOuter t).2.2 : ℝ) ≤ 2 * T := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  have hnmem : (wExtractedOriginal t.1).2.1 ∈ N := hm.2.2.2.2.2.2.2.1
  have hd : (wGCDTuple (wExtractedOriginal t.1)).n₁ ∣
      (wExtractedOriginal t.1).2.1 := by
    rw [hv.N₁_eq]
    exact dvd_mul_left _ _
  refine ⟨hv.n₁_pos, ?_⟩
  exact (show ((wCorrelationOuter t).2.2 : ℝ) ≤ (wExtractedOriginal t.1).2.1 by
    exact_mod_cast Nat.le_of_dvd (hN _ hnmem) hd).trans (hNT _ hnmem)

/-- Uniform actual inner and outer weights; no support enlargement of beta. -/
theorem direct_actual_weights (k j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X →
      ∀ (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (a : ℤ)
        (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey)
        (β γ ζ : ℕ → ℝ),
      (∀ n ∈ N, 0 < n) → (∀ q ∈ Q, 0 < q) →
      (∀ n ∈ N, (n : ℝ) ≤ X) → (∀ q ∈ Q, (q : ℝ) ≤ X) →
      0 ≤ R → 0 ≤ S → R ≤ X → S ≤ X →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau j n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau j n : ℝ)) →
      ∀ t ∈ wExtractedKeyFiber H N Q a P R S ξ b K,
        |wCorrelationInnerWeight K (betaClean β a) ζ t| ≤ (C * X ^ δ) ^ 2 ∧
        |wCorrelationOuterWeight K (betaClean β a)
          (factorConvolution γ (betaLowOmega ζ ξ)) γ (wCorrelationOuter t)| ≤
            (C * X ^ δ) ^ 3 := by
  obtain ⟨C, hC, henv⟩ := direct_fixedOrder_envelopes k j hδ
  refine ⟨C, hC, ?_⟩
  intro X hX H N Q a P R S ξ b K β γ ζ hN hQ hNX hQX hR hS hRX hSX hβ hγ hζ t ht
  obtain ⟨hb, hg, hz, hc⟩ := henv X hX N β γ ζ a ξ hNX hβ hγ hζ
  obtain ⟨hr, hq, hn, hs, hn'⟩ := direct_coefficient_support hN hQ ht
  have hrf : ((K.2 * (wCorrelationOuter t).2.1 : ℕ) : ℝ) ≤ X :=
    (show ((K.2 * (wCorrelationOuter t).2.1 : ℕ) : ℝ) ≤ ⌊R⌋₊ by
      exact_mod_cast (mem_Ioc.mp hr).2).trans ((Nat.floor_le hR).trans hRX)
  have hsf : (((K.1.2.2.1 * K.1.2.2.2.2 / K.2) * t.1.1.2.2 : ℕ) : ℝ) ≤ X :=
    (show (((K.1.2.2.1 * K.1.2.2.2.2 / K.2) * t.1.1.2.2 : ℕ) : ℝ) ≤ ⌊S⌋₊ by
      exact_mod_cast (mem_Ioc.mp hs).2).trans ((Nat.floor_le hS).trans hSX)
  have hE : 0 ≤ C * X ^ δ := by positivity
  constructor
  · dsimp only [wCorrelationInnerWeight]
    rw [abs_mul, pow_two]
    exact mul_le_mul (hz _ hsf) (hb _ hn') (abs_nonneg _) hE
  · dsimp only [wCorrelationOuterWeight]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (C * X ^ δ) * (C * X ^ δ) * (C * X ^ δ) :=
        mul_le_mul (mul_le_mul (hg _ hrf) (hc _ (hQX _ hq)) (abs_nonneg _) hE)
          (hb _ hn) (abs_nonneg _) (mul_nonneg hE hE)
      _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
