import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionDomain
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryResonanceCount

/-!
# Excluding the degenerate beta diagonal on the retained IV.3 carrier

Primitivity forces `d₁*n = n₂` to have `n₂ = 1`. The original second
beta coordinate would then be `d ≤ x^η`, contradicting its lower support.
The nonzero differences below are derived from the actual support and mask,
not imposed on the final original carrier.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem iv3_resonance_difference_ne_zero_of_support
    {d d₁ n n₂ : ℕ} {T Y : ℝ} (hc : (d₁ * n).Coprime n₂)
    (hd : (d : ℝ) ≤ Y) (hN₂ : T ≤ (d * n₂ : ℕ)) (hYT : Y < T) :
    (d₁ : ℤ) * n - n₂ ≠ 0 := by
  intro he
  have he' : d₁ * n = n₂ := by exact_mod_cast sub_eq_zero.mp he
  have hn₂ : n₂ = 1 := by
    simpa only [he', Nat.coprime_self] using hc
  rw [hn₂, mul_one] at hN₂
  linarith

/-- Applies already to the original extracted carrier, before any section
or Gram reindexing. Only the first component of the five-small mask is needed. -/
theorem wFactorExtractionTuples_resonance_difference_ne_zero
    {N Q : Finset ℕ} (hN : ∀ m ∈ N, 0 < m) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S ξ T : ℝ}
    (hNT : ∀ m ∈ N, T ≤ (m : ℝ)) (hT : x ^ η < T)
    {z : WExtractedTuple}
    (hz : z ∈ wFactorExtractionTuples N Q a (c2FiveSmallMask x η) R S ξ) :
    let v := wGCDTuple (wExtractedOriginal z)
    (v.d₁ : ℤ) * v.n₁ - v.n₂ ≠ 0 := by
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hmask := (wExtracted_extraction_spec hz).2.2.2
  obtain ⟨_, _, _, _, _, _, _, _, hn₂, _⟩ :=
    mem_wFactorExtractionTuples_iff.mp hz
  apply iv3_resonance_difference_ne_zero_of_support hv.n_primitive
    hmask.1.1.1.1 _ hT
  have ht := hNT _ hn₂
  change T ≤ ((wExtractedOriginal z).2.2 : ℝ) at ht
  rwa [hv.N₂_eq] at ht

/-- The same exclusion in the reconstructed fixed support interface. -/
theorem wKSectionFixedSupport_resonance_difference_ne_zero
    {N : Finset ℕ} {a : ℤ} {x η R S T : ℝ}
    (hNT : ∀ m ∈ N, T ≤ (m : ℝ)) (hT : x ^ η < T)
    {K : WExtractedKey} {r n n₂ s : ℕ}
    (hf : wKSectionFixedCanonical K r n n₂ s)
    (hsup : wKSectionFixedSupport N a x η R S K r n n₂ s) :
    (K.1.2.1 : ℤ) * n - n₂ ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hf
  obtain ⟨_, _, _, hn₂, _, _, _, _, _, hd, _⟩ := hsup
  exact iv3_resonance_difference_ne_zero_of_support hc hd (hNT _ hn₂) hT

/-- Membership in an occupied key fiber supplies its own nonzero
difference, with the fixed key's `d₁`. -/
theorem wExtractedKeyFiber_resonance_difference_ne_zero
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ m ∈ N, 0 < m) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S ξ T : ℝ} {b : ℕ} {K : WExtractedKey}
    (hNT : ∀ m ∈ N, T ≤ (m : ℝ)) (hT : x ^ η < T)
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η) R S ξ b K) :
    let v := wGCDTuple (wExtractedOriginal t.1)
    (K.1.2.1 : ℤ) * v.n₁ - v.n₂ ≠ 0 := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hd := congrArg WGCDData.d₁ (wExtractedKeyFiber_kSection_data hN hQ ht)
  have he := wFactorExtractionTuples_resonance_difference_ne_zero hN hQ hNT hT hz
  dsimp only at he ⊢
  change (wGCDTuple (wExtractedOriginal t.1)).d₁ = K.1.2.1 at hd
  rwa [hd] at he

/-- Both exclusions for a pair with the same first beta index follow
from original membership. This does not assert any small-root cancellation. -/
theorem wExtractedKeyFiber_resonance_differences_ne_zero
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ m ∈ N, 0 < m) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S ξ T : ℝ} {b : ℕ} {K : WExtractedKey}
    (hNT : ∀ m ∈ N, T ≤ (m : ℝ)) (hT : x ^ η < T)
    {t u : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η) R S ξ b K)
    (hu : u ∈ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η) R S ξ b K)
    (hn : (wGCDTuple (wExtractedOriginal t.1)).n₁ =
      (wGCDTuple (wExtractedOriginal u.1)).n₁) :
    let v := wGCDTuple (wExtractedOriginal t.1)
    let v' := wGCDTuple (wExtractedOriginal u.1)
    ((K.1.2.1 : ℤ) * v.n₁ - v.n₂ ≠ 0) ∧
      ((K.1.2.1 : ℤ) * v.n₁ - v'.n₂ ≠ 0) := by
  refine ⟨wExtractedKeyFiber_resonance_difference_ne_zero hN hQ hNT hT ht, ?_⟩
  rw [hn]
  exact wExtractedKeyFiber_resonance_difference_ne_zero hN hQ hNT hT hu

theorem iv3_resonance_support_gap
    {x η ε T : ℝ} (hx : 1 < x) (hη : η < ε) (hT : x ^ ε ≤ T) :
    x ^ η < T :=
  (Real.rpow_lt_rpow_of_exponent_lt hx hη).trans_le hT

/-- A finite weighted count using only canonicality, retained fixed support,
and zero resonance. In particular neither difference is a free hypothesis.
These support predicates are the ones reconstructed from actual membership. -/
theorem iv3_resonance_sum_le_const_mul_of_fixedSupport
    {N : Finset ℕ} {a h : ℤ} {x η R S T : ℝ}
    (ha : a ≠ 0) (hh : h ≠ 0)
    (hNT : ∀ m ∈ N, T ≤ (m : ℝ)) (hT : x ^ η < T)
    {K : WExtractedKey} {r n n₂' s' : ℕ}
    (hf' : wKSectionFixedCanonical K r n n₂' s')
    (hsup' : wKSectionFixedSupport N a x η R S K r n n₂' s')
    (F : Finset (ℕ × ℕ × ℤ))
    (hF : ∀ t ∈ F, wKSectionFixedCanonical K r n t.1 t.2.1 ∧
      wKSectionFixedSupport N a x η R S K r n t.1 t.2.1 ∧
      iv3CorrelationNumerator K.1.2.1 n t.1 n₂' t.2.1 s' a h t.2.2 = 0)
    (w : ℕ × ℕ × ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ t ∈ F, w t ≤ B) :
    (∑ t ∈ F, w t) ≤ B *
      (∑ n₂ ∈ (h * n₂' * s').natAbs.divisors,
        (fouvryTau 2 ((h * n₂' * s') *
          ((K.1.2.1 : ℤ) * n - n₂)).natAbs : ℝ)) := by
  have hcoords {j s : ℕ} (hf : wKSectionFixedCanonical K r n j s) :
      0 < j ∧ 0 < s ∧ (K.1.2.1 * n).Coprime j := by
    obtain ⟨_, _, _, _, _, _, hs, _, hj, _, _, _, _, _, hc, _⟩ := hf
    exact ⟨hj, hs, hc⟩
  have hn₂' : (n₂' : ℤ) ≠ 0 := by
    exact_mod_cast (hcoords hf').1.ne'
  have hs' : (s' : ℤ) ≠ 0 := by
    exact_mod_cast (hcoords hf').2.1.ne'
  apply iv3_resonance_sum_le_const_mul ha (mul_ne_zero (mul_ne_zero hh hn₂') hs')
    (wKSectionFixedSupport_resonance_difference_ne_zero hNT hT hf' hsup') F _ w hB hw
  intro t ht
  have hc := hcoords (hF t ht).1
  exact ⟨hc.1, hc.2.1, hc.2.2,
    wKSectionFixedSupport_resonance_difference_ne_zero hNT hT
      (hF t ht).1 (hF t ht).2.1, (hF t ht).2.2⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
