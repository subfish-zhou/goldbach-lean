import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionReconstruction

/-!
# The full-level, paid-floor IV.3 k₁ carrier

After reconstruction, both original factor supports and all beta masks are
constant along the section. Canonical extraction and compatibility leave
explicit coprimalities in `k₁`; the floor frequency bound is an interval.
This is an exact carrier identity, not a bound for an arbitrary masked sum.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Original support, compatibility and five-small/low-omega conditions
which do not vary with `k₁`. The finite beta carrier may be arbitrary. -/
def wKSectionFixedSupport (N : Finset ℕ) (a : ℤ) (x η R S : ℝ)
    (K : WExtractedKey) (r n₁ n₂ s : ℕ) : Prop :=
  let N₁ := K.1.1 * K.1.2.1 * n₁
  let N₂ := K.1.1 * n₂
  let q₂ := K.1.2.2.1 * K.1.2.2.2.2 * (r * s)
  K.2 * r ≤ ⌊R⌋₊ ∧ wKSectionDeltaPrime K * s ≤ ⌊S⌋₊ ∧
  N₁ ∈ N ∧ N₂ ∈ N ∧
  a.natAbs.Coprime (K.1.2.2.1 * K.1.2.2.2.1) ∧ a.natAbs.Coprime q₂ ∧
  N₁.Coprime (K.1.2.2.1 * K.1.2.2.2.1) ∧ N₂.Coprime q₂ ∧
  Nat.ModEq K.1.2.2.1 N₁ N₂ ∧
  (K.1.1 : ℝ) ≤ x ^ η ∧ (K.1.2.1 : ℝ) ≤ x ^ η ∧
  (K.1.2.2.1 : ℝ) ≤ x ^ η ∧ (K.1.2.2.2.1 : ℝ) ≤ x ^ η ∧
  (K.1.2.2.2.2 : ℝ) ≤ x ^ η ∧
  (N₁.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
  (N₂.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
  ((wKSectionDeltaPrime K * s).primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
  s.Coprime K.2

/-- The complete varying arithmetic mask, not an unspecified predicate. -/
def wKSectionCoprime (K : WExtractedKey) (a : ℤ) (r n₁ s k : ℕ) : Prop :=
  k.Coprime K.1.2.2.1 ∧ k.Coprime (K.1.2.2.2.2 * (r * s)) ∧
    a.natAbs.Coprime k ∧ (K.1.1 * K.1.2.1 * n₁).Coprime k

theorem wKSectionTuple_factor_iff
    {N : Finset ℕ} {a : ℤ} {x η R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ} (h : ℤ)
    (hf : wKSectionFixedCanonical K r n₁ n₂ s) (hk : 0 < k)
    (hkδ : k.Coprime K.1.2.2.1)
    (hkr : k.Coprime (K.1.2.2.2.2 * (r * s)))
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2) :
    (wKSectionTuple K r n₁ n₂ s h k).1 ∈
        wFactorExtractionTuples N (Ioc 0 ⌊R * S⌋₊) a
          (c2FiveSmallMask x η) R S (highOmegaCutoff x) ↔
      wKSectionFixedSupport N a x η R S K r n₁ n₂ s ∧
        k ≤ ⌊R * S⌋₊ / (K.1.2.2.1 * K.1.2.2.2.1) ∧
        a.natAbs.Coprime k ∧ (K.1.1 * K.1.2.1 * n₁).Coprime k := by
  have hv := wKSectionData_valid hf hk hkδ hkr
  have hr := hf.2.2.2.2.2.1
  have hs := hf.2.2.2.2.2.2.1
  have hδδ₁ := Nat.mul_pos hf.2.2.1 hf.2.2.2.1
  have hp : (K.2 * r) * (wKSectionDeltaPrime K * s) =
      K.1.2.2.1 * K.1.2.2.2.2 * (r * s) := by
    calc
      _ = (K.2 * wKSectionDeltaPrime K) * (r * s) := by ring
      _ = _ := by rw [he]
  have hcan : wGCDTuple
      ((K.1.2.2.1 * K.1.2.2.2.1 * k, K.1.2.2.1 * K.1.2.2.2.2 * (r * s)),
        (K.1.1 * K.1.2.1 * n₁, K.1.1 * n₂)) = wKSectionData K r n₁ n₂ s k :=
    hv.eq_canonical.symm
  have hdg := hv.d_eq.symm
  have hδg := hv.δ_eq.symm
  change (K.1.1 * K.1.2.1 * n₁).gcd (K.1.1 * n₂) = K.1.1 at hdg
  change (K.1.2.2.1 * K.1.2.2.2.1 * k).gcd
    (K.1.2.2.1 * K.1.2.2.2.2 * (r * s)) = K.1.2.2.1 at hδg
  have hq : K.1.2.2.1 * K.1.2.2.2.1 * k ∈ Ioc 0 ⌊R * S⌋₊ ↔
      k ≤ ⌊R * S⌋₊ / (K.1.2.2.1 * K.1.2.2.2.1) := by
    simp only [mem_Ioc, Nat.mul_pos hδδ₁ hk, true_and,
      Nat.le_div_iff_mul_le hδδ₁, mul_comm k]
  have haq : a.natAbs.Coprime (K.1.2.2.1 * K.1.2.2.2.1 * k) ↔
      a.natAbs.Coprime (K.1.2.2.1 * K.1.2.2.2.1) ∧ a.natAbs.Coprime k :=
    Nat.coprime_mul_iff_right
  have hnq : (K.1.1 * K.1.2.1 * n₁).Coprime (K.1.2.2.1 * K.1.2.2.2.1 * k) ↔
      (K.1.1 * K.1.2.1 * n₁).Coprime (K.1.2.2.1 * K.1.2.2.2.1) ∧
        (K.1.1 * K.1.2.1 * n₁).Coprime k := Nat.coprime_mul_iff_right
  rw [mem_wFactorExtractionTuples_iff]
  dsimp only [wKSectionTuple]
  rw [hp]
  simp only [mem_reducedModuli_fullLevel_iff, WCompatible, c2FiveSmallMask,
    wSecondExtractionDivisor, hcan, wKSectionData, hdg, hδg, hq, haq, hnq]
  dsimp only [wKSectionFixedSupport]
  constructor
  · intro ht
    tauto
  · intro ht
    have hrbox := (positive_factor_box_iff hΔ hr).mpr
      (mem_Ioc.mpr ⟨hr, (Nat.le_div_iff_mul_le hΔ).mpr
        (by simpa only [mul_comm r] using ht.1.1)⟩)
    have hsbox := (positive_factor_box_iff hΔ' hs).mpr
      (mem_Ioc.mpr ⟨hs, (Nat.le_div_iff_mul_le hΔ').mpr
        (by simpa only [mul_comm s] using ht.1.2.1)⟩)
    have hprod := supported_product_mem_fullLevel hR hS
      (mem_Ioc.mpr ⟨Nat.mul_pos hΔ hr, ht.1.1⟩)
      (mem_Ioc.mpr ⟨Nat.mul_pos hΔ' hs, ht.1.2.1⟩)
    rw [hp] at hprod
    have he' := he.symm
    tauto

def wKSectionLower (M Z : ℝ) (K : WExtractedKey) (r s : ℕ) (h : ℤ) : ℕ :=
  max 1 ⌈(h.natAbs : ℝ) * M * K.1.2.2.1 /
    (((K.1.2.2.1 * K.1.2.2.2.2 * (r * s) : ℕ) : ℝ) *
      (K.1.2.2.1 * K.1.2.2.2.1 : ℕ) * Z)⌉₊

def wKSectionUpper (R S : ℝ) (K : WExtractedKey) : ℕ :=
  ⌊R * S⌋₊ / (K.1.2.2.1 * K.1.2.2.2.1)

/-- Exact membership of a reconstructed original tuple. The extraction
equation, both supports, the gcd key, the signed shell and the paid floor
cutoff are all accounted for. No varying coefficient is discarded. -/
theorem wKSectionTuple_mem_key_iff
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ} {h : ℤ} {b : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2) :
    wKSectionTuple K r n₁ n₂ s h k ∈
        wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
          (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K ↔
      wKSectionFixedSupport N a x η R S K r n₁ n₂ s ∧
      2 ^ b ≤ h.natAbs ∧ h.natAbs < 2 ^ (b + 1) ∧
      k ∈ Icc (wKSectionLower M Z K r s h) (wKSectionUpper R S K) ∧
      wKSectionCoprime K a r n₁ s k := by
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hnecess (ht : wKSectionTuple K r n₁ n₂ s h k ∈
      wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) :
      0 < k ∧ k.Coprime K.1.2.2.1 ∧
        k.Coprime (K.1.2.2.2.2 * (r * s)) := by
    have hc := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1
      hf.2.2.1 hf.2.2.2.1 ht
    have hz := (mem_wExtractedFrequencies_iff.mp
      (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
    have hv := (wExtractedOriginal_valid hN hQ hz).1
    rw [hc] at hv
    exact ⟨hv.k₁_pos, hv.k₁_δ, (Nat.coprime_mul_iff_left.mp hv.k_primitive).2⟩
  by_cases hc : 0 < k ∧ k.Coprime K.1.2.2.1 ∧
      k.Coprime (K.1.2.2.2.2 * (r * s))
  · obtain ⟨hk, hkδ, hkr⟩ := hc
    have hv := wKSectionData_valid hf hk hkδ hkr
    have hcan := wKSectionTuple_canonical hf hk hkδ hkr he h
    have hkey : wExtractedKey (wKSectionTuple K r n₁ n₂ s h k).1 = K := by
      rw [wExtractedKey, hcan]
      rfl
    have hfactor := wKSectionTuple_factor_iff (N := N) (a := a) (x := x) (η := η)
      hR hS h hf hk hkδ hkr hΔ hΔ' he
    have hg := hv.δ_eq.symm
    rw [Nat.gcd_comm] at hg
    have hcut := wFloorCutoff_factor_interval_iff hM hZ
      (Nat.mul_pos (Nat.mul_pos hf.2.2.1 hf.2.2.2.2.1)
        (Nat.mul_pos hf.2.2.2.2.2.1 hf.2.2.2.2.2.2.1))
      (Nat.mul_pos hf.2.2.1 hf.2.2.2.1) hg h
    dsimp only [wKSectionData] at hcut
    have hlo : 1 ≤ k := hk
    rw [mem_wExtractedKeyFiber_iff, mem_frequencyBlock_iff,
      mem_wExtractedFrequencies_iff, hfactor, hkey,
      wKSectionTuple_original he]
    dsimp only [WGCDData.original, wKSectionData, wKSectionTuple]
    have hfreq : (-(wFloorCutoff M Z (K.1.2.2.1 * K.1.2.2.2.1 * k)
        (K.1.2.2.1 * K.1.2.2.2.2 * (r * s)) : ℤ) ≤ h ∧
        h ≤ wFloorCutoff M Z (K.1.2.2.1 * K.1.2.2.2.1 * k)
          (K.1.2.2.1 * K.1.2.2.2.2 * (r * s))) ↔
        h.natAbs ≤ wFloorCutoff M Z (K.1.2.2.1 * K.1.2.2.2.1 * k)
          (K.1.2.2.1 * K.1.2.2.2.2 * (r * s)) := by omega
    rw [hfreq]
    have hswap : wFloorCutoff M Z (K.1.2.2.1 * K.1.2.2.2.1 * k)
        (K.1.2.2.1 * K.1.2.2.2.2 * (r * s)) =
        wFloorCutoff M Z (K.1.2.2.1 * K.1.2.2.2.2 * (r * s))
          (K.1.2.2.1 * K.1.2.2.2.1 * k) := by
      simp only [wFloorCutoff, Nat.lcm_comm]
    rw [hswap, hcut]
    simp only [wKSectionLower, wKSectionUpper, mem_Icc, max_le_iff,
      wKSectionCoprime, hlo, true_and]
    constructor
    · rintro ⟨⟨⟨⟨hsup, hbound, ha, hn⟩, hcut⟩, hblo, hbhi⟩, _⟩
      exact ⟨hsup, hblo, hbhi, ⟨hcut, hbound⟩, hkδ, hkr, ha, hn⟩
    · rintro ⟨hsup, hblo, hbhi, ⟨hcut, hbound⟩, _, _, ha, hn⟩
      exact ⟨⟨⟨⟨hsup, hbound, ha, hn⟩, hcut⟩, hblo, hbhi⟩, trivial⟩
  · constructor
    · exact fun ht => (hc (hnecess ht)).elim
    · intro ht
      have hk : 0 < k := lt_of_lt_of_le (by decide : 0 < 1)
        ((le_max_left 1 _).trans (mem_Icc.mp ht.2.2.2.1).1)
      exact (hc ⟨hk, ht.2.2.2.2.1, ht.2.2.2.2.2.1⟩).elim

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
