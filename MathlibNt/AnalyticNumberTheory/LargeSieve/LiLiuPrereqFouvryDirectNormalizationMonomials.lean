import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalization

/-!
# Local monomials after reciprocal payment

These are algebraic normalization tools, not asserted producers of main
or secondary energy. Exponents are arbitrary and are only enlarged to
global scales when their post-payment values are nonnegative.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The small key costs at most Y^3 in D and Y^5 in D'. -/
theorem directLocalScale_key_bounds {Y : ℝ} (hY : 0 ≤ Y)
    {K : WExtractedKey} (hK : K ∈ wExtractedKeyBox Y) :
    (K.D : ℝ) ≤ Y ^ 3 ∧ (K.D' : ℝ) ≤ Y ^ 5 := by
  have hk := mem_wExtractedKeyBox_iff.mp hK
  have hh {n : ℕ} (hn : n ≤ ⌊Y⌋₊) : (n : ℝ) ≤ Y :=
    (Nat.cast_le.mpr hn).trans (Nat.floor_le hY)
  have hD : (K.D : ℝ) ≤ Y ^ 3 := by
    unfold WExtractedKey.D
    push_cast
    calc
      _ ≤ Y * Y * Y := by
        exact mul_le_mul (mul_le_mul (hh hk.2.2.1) (hh hk.2.2.2.1)
          (Nat.cast_nonneg _) hY) (hh hk.2.2.2.2.1) (Nat.cast_nonneg _) (mul_nonneg hY hY)
      _ = _ := by ring
  refine ⟨hD, ?_⟩
  unfold WExtractedKey.D'
  push_cast
  calc
    _ ≤ Y * Y * Y ^ 3 := by
      exact mul_le_mul (mul_le_mul (hh hk.1) (hh hk.2.1)
        (Nat.cast_nonneg _) hY) hD (Nat.cast_nonneg _) (mul_nonneg hY hY)
    _ = _ := by ring

/-- Global upper coordinates are consequences of an actual full-level member.
This theorem does not itself replace any local scale in a denominator. -/
theorem directLocalScale_fullLevel_coordinates
    {H : ℕ → ℕ → ℕ} {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {L R S : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    {a : ℤ} {P : WOriginalTuple → Prop} {ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N (Ioc 0 ⌊L⌋₊) a P R S ξ b K) j positive) :
    (2 : ℝ) ^ j 1 ≤ L ∧ (2 : ℝ) ^ j 3 ≤ R ∧ (2 : ℝ) ^ j 4 ≤ S := by
  have hQ : ∀ q ∈ Ioc 0 ⌊L⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hf := (mem_filter.mp ht).1
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp hf).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  have hq := (mem_filter.mp (wExtractedOriginal_reducedModuli hz).1).1
  have hk : (wGCDTuple (wExtractedOriginal t.1)).k₁ ≤ ⌊L⌋₊ :=
    (Nat.le_of_dvd (hQ _ hq) hv.k₁_dvd).trans (mem_Ioc.mp hq).2
  have hb := wAnalyticDyadicBlock_bounds hN hQ ht
  exact ⟨(hb 1).1.trans ((Nat.cast_le.mpr hk).trans (Nat.floor_le hL)),
    (hb 3).1.trans ((Nat.cast_le.mpr (mem_Ioc.mp hm.2.2.1).2).trans (Nat.floor_le hR)),
    (hb 4).1.trans ((Nat.cast_le.mpr (mem_Ioc.mp hm.2.2.2.1).2).trans (Nat.floor_le hS))⟩


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
