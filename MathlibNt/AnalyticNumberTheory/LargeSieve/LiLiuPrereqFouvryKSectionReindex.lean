import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionDomain

/-!
# Exact reindexing of the remaining IV.3 section

The signed dyadic rectangle, the five prefix caps and the Lemma 7 cell are
retained. The only varying restrictions are an explicit interval and
coprimalities. This does not yet freeze the small-root phase or pay for
the residue classes needed in an application of the progression bound.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open _root_.LiLiuPrereqFouvry.CoprimePartition

def wKSectionFixedGrid (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (r n₁ n₂ s : ℕ) (h : ℤ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) : Prop :=
  Nat.log 2 h.natAbs = j 0 ∧ Nat.log 2 n₁ = j 2 ∧
  Nat.log 2 r = j 3 ∧ Nat.log 2 s = j 4 ∧
  h.natAbs ≤ cap 0 ∧ n₁ ≤ cap 2 ∧ r ≤ cap 3 ∧ s ≤ cap 4 ∧
  decide (0 < h) = positive ∧
  cell (wCoprimePairBound N S) (wCoprimeOrder x)
    (matrixColor (wCoprimePairBound N S) (wCoprimeOrder x) (n₂, n₁ * s)) = c

def wKSectionGridLower (M Z : ℝ) (K : WExtractedKey) (r s : ℕ)
    (h : ℤ) (j : Fin 5 → ℕ) : ℕ :=
  max (wKSectionLower M Z K r s h) (2 ^ j 1)

def wKSectionGridUpper (R S : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ) : ℕ :=
  min (wKSectionUpper R S K) (min (cap 1) (2 ^ (j 1 + 1) - 1))

/-- A filter of an explicitly given interval, with no hidden membership
test. Every condition apart from `wKSectionCoprime` is fixed on the section. -/
def wKSectionCarrier (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (r n₁ n₂ s : ℕ) (h : ℤ) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) : Finset ℕ :=
  (Icc (wKSectionGridLower M Z K r s h j) (wKSectionGridUpper R S K j cap)).filter
    (fun k => wKSectionFixedSupport N a x η R S K r n₁ n₂ s ∧
      2 ^ b ≤ h.natAbs ∧ h.natAbs < 2 ^ (b + 1) ∧
      wKSectionFixedGrid x N S r n₁ n₂ s h j cap positive c ∧
      wKSectionCoprime K a r n₁ s k)

def wKSectionSlice (U : Finset (WExtractedTuple × ℤ))
    (r n₁ n₂ s : ℕ) (h : ℤ) : Finset (WExtractedTuple × ℤ) :=
  U.filter (fun t => t.1.1.2.1 = r ∧
    (wGCDTuple (wExtractedOriginal t.1)).n₁ = n₁ ∧
    (wGCDTuple (wExtractedOriginal t.1)).n₂ = n₂ ∧ t.1.1.2.2 = s ∧ t.2 = h)

private theorem grid_filter_iff
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {r n₁ n₂ s k : ℕ}
    {h : ℤ} {b : ℕ} (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    (ht : wKSectionTuple K r n₁ n₂ s h k ∈
      wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) :
    wKSectionTuple K r n₁ n₂ s h k ∈
      wCoprimeFiber x N S
        (wAnalyticPrefix (wAnalyticDyadicBlock
          (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
            (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap) c ↔
      wKSectionFixedGrid x N S r n₁ n₂ s h j cap positive c ∧
        Nat.log 2 k = j 1 ∧ k ≤ cap 1 := by
  have hcan := wKSectionTuple_canonical_of_mem hN
    (fun _ hq => (mem_Ioc.mp hq).1) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 ht
  have hcoords : wAnalyticCoordinates (wKSectionTuple K r n₁ n₂ s h k) =
      ![h.natAbs, k, n₁, r, s] := by
    unfold wAnalyticCoordinates
    rw [hcan]
    rfl
  have hlabel : wCoprimeLabel x N S (wKSectionTuple K r n₁ n₂ s h k) =
      cell (wCoprimePairBound N S) (wCoprimeOrder x)
        (matrixColor (wCoprimePairBound N S) (wCoprimeOrder x) (n₂, n₁ * s)) := by
    unfold wCoprimeLabel wCoprimePair
    rw [hcan]
    rfl
  simp only [wCoprimeFiber, wAnalyticPrefix, wAnalyticDyadicBlock, mem_filter,
    ht, true_and, wAnalyticDyadicKey, hcoords, funext_iff,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ, hlabel]
  change (((Nat.log 2 h.natAbs = j 0 ∧ Nat.log 2 k = j 1 ∧
      Nat.log 2 n₁ = j 2 ∧ Nat.log 2 r = j 3 ∧ Nat.log 2 s = j 4) ∧
      decide (0 < h) = positive) ∧
      h.natAbs ≤ cap 0 ∧ k ≤ cap 1 ∧ n₁ ≤ cap 2 ∧ r ≤ cap 3 ∧ s ≤ cap 4) ∧
      _ = c ↔ _
  unfold wKSectionFixedGrid
  tauto

/-- The actual coprime-cell/dyadic/prefix membership has no further
varying restrictions beyond the displayed arithmetic carrier. -/
theorem wKSectionTuple_mem_filtered_iff
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ} {h : ℤ} {b : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) :
    wKSectionTuple K r n₁ n₂ s h k ∈
      wCoprimeFiber x N S
        (wAnalyticPrefix (wAnalyticDyadicBlock
          (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
            (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap) c ↔
      k ∈ wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c := by
  have hbase := wKSectionTuple_mem_key_iff (k := k) (h := h) (b := b) (a := a)
    (x := x) (η := η) hN hR hS hM hZ hf hΔ hΔ' he
  have hlog (hk : 0 < k) : Nat.log 2 k = j 1 ↔
      2 ^ j 1 ≤ k ∧ k ≤ 2 ^ (j 1 + 1) - 1 := by
    rw [Nat.log_eq_iff (Or.inr ⟨by decide, hk.ne'⟩)]
    have hp : 0 < 2 ^ (j 1 + 1) := by positivity
    omega
  constructor
  · intro ht
    have hb := (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).1
    have hg := (grid_filter_iff hN hf j cap positive c hb).mp ht
    obtain ⟨hsup, hblo, hbhi, hint, hcp⟩ := hbase.mp hb
    have hk : 0 < k := lt_of_lt_of_le (by decide : 0 < 1)
      ((le_max_left 1 _).trans (mem_Icc.mp hint).1)
    obtain ⟨hl, hu⟩ := (hlog hk).mp hg.2.1
    apply mem_filter.mpr
    refine ⟨?_, hsup, hblo, hbhi, hg.1, hcp⟩
    simpa only [wKSectionGridLower, wKSectionGridUpper, mem_Icc,
      max_le_iff, le_min_iff] using
      And.intro (And.intro (mem_Icc.mp hint).1 hl)
        (And.intro (mem_Icc.mp hint).2 (And.intro hg.2.2 hu))
  · intro hk
    obtain ⟨hint, hsup, hblo, hbhi, hg, hcp⟩ := mem_filter.mp hk
    simp only [wKSectionGridLower, wKSectionGridUpper, mem_Icc,
      max_le_iff, le_min_iff] at hint
    have hpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 1)
      ((le_max_left 1 _).trans hint.1.1)
    have hb := hbase.mpr ⟨hsup, hblo, hbhi,
      mem_Icc.mpr ⟨hint.1.1, hint.2.1⟩, hcp⟩
    exact (grid_filter_iff hN hf j cap positive c hb).mpr
      ⟨hg, (hlog hpos).mpr ⟨hint.1.2, hint.2.2.2⟩, hint.2.2.1⟩

/-- Exact summed reindexing of real original tuples, for arbitrary
additive weights. In particular the small-root product and both signed
coefficients may be inserted without changing any domain condition. -/
theorem sum_wKSectionSlice
    {A : Type*} [AddCommMonoid A]
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    {K : WExtractedKey} {r n₁ n₂ s : ℕ} {h : ℤ} {b : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    (F : WExtractedTuple × ℤ → A) :
    ∑ t ∈ wKSectionSlice
      (wCoprimeFiber x N S
        (wAnalyticPrefix (wAnalyticDyadicBlock
          (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
            (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap) c)
      r n₁ n₂ s h, F t =
    ∑ k ∈ wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c,
      F (wKSectionTuple K r n₁ n₂ s h k) := by
  let U := wCoprimeFiber x N S
    (wAnalyticPrefix (wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap) c
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hU : U ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K := by
    intro t ht
    exact (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).1
  have hrec {t : WExtractedTuple × ℤ} (ht : t ∈ wKSectionSlice U r n₁ n₂ s h) :
      wKSectionTuple K r n₁ n₂ s h (wGCDTuple (wExtractedOriginal t.1)).k₁ = t := by
    obtain ⟨htu, hr, hn₁, hn₂, hs, hh⟩ := mem_filter.mp ht
    have ht := wExtractedKeyFiber_kSection_reconstruct hN hQ (hU htu)
    simpa only [hr, hn₁, hn₂, hs, hh] using ht
  have hmem (k : ℕ) := wKSectionTuple_mem_filtered_iff (k := k) (h := h) (b := b)
    (a := a) (x := x) (η := η) hN hR hS hM hZ hf hΔ hΔ' he j cap positive c
  refine sum_bij (fun t _ => (wGCDTuple (wExtractedOriginal t.1)).k₁) ?_ ?_ ?_ ?_
  · intro t ht
    apply (hmem _).mp
    rw [hrec ht]
    exact (mem_filter.mp ht).1
  · intro t ht u hu htu
    rw [← hrec ht, ← hrec hu, htu]
  · intro k hk
    have hu := (hmem k).mpr hk
    have hcan := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1
      hf.2.2.1 hf.2.2.2.1 (hU hu)
    refine ⟨wKSectionTuple K r n₁ n₂ s h k, mem_filter.mpr ⟨hu, ?_⟩, ?_⟩
    · rw [hcan]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [hcan]
      rfl
  · intro t ht
    rw [hrec ht]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
