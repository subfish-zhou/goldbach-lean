import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticBox

/-!
# Actual local frequency scales

The floor cutoff is the already-paid actual cutoff, not a hypothetical
replacement. The ceiling version keeps its extra unit. All dyadic claims
below have an actual member; an empty block is handled separately.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Exact original lcm on a fixed extracted key. -/
theorem directLocalScale_lcm_eq
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    (wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 =
      K.D * (wGCDTuple (wExtractedOriginal t.1)).k₁ * t.1.1.2.1 * t.1.1.2.2 := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  rw [hv.lcm_eq, wExtracted_k₂_eq hN hQ hz, (wExtractedKeyFiber_moduli ht).1]
  exact Nat.mul_assoc _ _ _ |>.symm

/-- The lcm is compared with the local k,r,s scales, never the global level. -/
theorem directLocalScale_lcm_le
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N Q a P R S ξ b K) j positive) :
    ((wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 : ℝ) ≤
      8 * ((K.D : ℝ) * 2 ^ j 1 * 2 ^ j 3 * 2 ^ j 4) := by
  rw [directLocalScale_lcm_eq hN hQ (mem_filter.mp ht).1]
  push_cast
  have hb := wAnalyticDyadicBlock_bounds hN hQ ht
  have hk : ((wGCDTuple (wExtractedOriginal t.1)).k₁ : ℝ) ≤ 2 * 2 ^ j 1 := (hb 1).2.le
  have hr : (t.1.1.2.1 : ℝ) ≤ 2 * 2 ^ j 3 := (hb 3).2.le
  have hs : (t.1.1.2.2 : ℝ) ≤ 2 * 2 ^ j 4 := (hb 4).2.le
  calc
    _ ≤ (K.D : ℝ) * (2 * 2 ^ j 1) * (2 * 2 ^ j 3) * (2 * 2 ^ j 4) := by
      gcongr
    _ = _ := by ring

/-- The true floor-retained local H has no rounding loss. -/
theorem directLocalScale_floor_frequency_le
    {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive) :
    (2 : ℝ) ^ j 0 ≤
      8 * ((K.D : ℝ) * 2 ^ j 1 * 2 ^ j 3 * 2 ^ j 4) / M * Z := by
  have hf := (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp (mem_filter.mp ht).1).1).1
  obtain ⟨_, hlo, hhi⟩ := mem_wExtractedFrequencies_iff.mp hf
  have habs : t.2.natAbs ≤ wFloorCutoff M Z
      (wExtractedOriginal t.1).1.1 (wExtractedOriginal t.1).1.2 := by
    have hi := abs_le.mpr ⟨hlo, hhi⟩
    rw [← Int.natCast_natAbs] at hi
    exact_mod_cast hi
  have hfloor : (t.2.natAbs : ℝ) ≤
      ((wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 : ℝ) / M * Z :=
    (Nat.cast_le.mpr habs).trans (Nat.floor_le (by positivity))
  exact (wAnalyticDyadicBlock_bounds hN hQ ht 0).1.trans
    (hfloor.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (directLocalScale_lcm_le hN hQ ht) hM.le) hZ))


/-- Recover x=4MT before any enlargement to global parameters. -/
theorem directLocalScale_frequency_change_variables
    {M T x A Z : ℝ} (hM : M ≠ 0) (hT : T ≠ 0) (hx : x = 4 * M * T) :
    8 * A / M * Z = 32 * A * Z * T / x := by
  rw [hx]
  field_simp
  ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
