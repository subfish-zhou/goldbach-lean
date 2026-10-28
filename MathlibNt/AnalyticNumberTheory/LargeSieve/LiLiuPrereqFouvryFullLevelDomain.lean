import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFrequencyBlocks

/-!
# The genuine full-level modulus carrier

Only the complete positive interval is used here. No arbitrary membership
mask is absorbed into a well-factorable coefficient. The inner factor has
an exact floor interval and explicitly retained arithmetic restrictions;
the filtered fiber is not asserted to be an unweighted interval.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem mem_reducedModuli_fullLevel_iff (L : ℝ) (a : ℤ) (q : ℕ) :
    q ∈ reducedModuli (Ioc 0 ⌊L⌋₊) a ↔
      q ∈ Ioc 0 ⌊L⌋₊ ∧ a.natAbs.Coprime q := by
  rw [reducedModuli, Finset.mem_filter]
  simp only [Int.gcd_def, Int.natAbs_natCast,
    Nat.coprime_iff_gcd_eq_one]


theorem supported_product_mem_fullLevel {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    {r s : ℕ} (hr : r ∈ Ioc 0 ⌊R⌋₊) (hs : s ∈ Ioc 0 ⌊S⌋₊) :
    r * s ∈ Ioc 0 ⌊R * S⌋₊ := by
  obtain ⟨hr0, hrR⟩ := mem_Ioc.mp hr
  obtain ⟨hs0, hsS⟩ := mem_Ioc.mp hs
  refine mem_Ioc.mpr ⟨Nat.mul_pos hr0 hs0, Nat.le_floor ?_⟩
  rw [Nat.cast_mul]
  exact mul_le_mul
    ((Nat.cast_le.mpr hrR).trans (Nat.floor_le hR))
    ((Nat.cast_le.mpr hsS).trans (Nat.floor_le hS)) (Nat.cast_nonneg _) hR


/-- The real interval for a positive varying factor. Both coordinate caps
in the broad extraction box are consequences of the product cap. -/
theorem positive_factor_box_iff {d k F : ℕ} (hd : 0 < d) (hk : 0 < k) :
    d ∈ Ioc 0 F ∧ k ∈ Ioc 0 F ∧ d * k ≤ F ↔ k ∈ Ioc 0 (F / d) := by
  simp only [mem_Ioc, hd, hk, true_and, Nat.le_div_iff_mul_le hd, mul_comm k d]
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨(Nat.le_mul_of_pos_right d hk).trans h,
      (Nat.le_mul_of_pos_left k hd).trans h, h⟩


theorem wExtractedOriginal_reducedModuli {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {z : WExtractedTuple}
    (hz : z ∈ wFactorExtractionTuples N Q a P R S ξ) :
    (wExtractedOriginal z).1.1 ∈ reducedModuli Q a ∧
      (wExtractedOriginal z).1.2 ∈ reducedModuli Q a := by
  have he := mem_wFactorExtractionTuples_iff.mp hz
  dsimp only [wExtractedOriginal]
  tauto

theorem wUniformCutoff_le_fullLevel {M Z L : ℝ}
    (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    {q r : ℕ} (hq : q ∈ Ioc 0 ⌊L⌋₊) (hr : r ∈ Ioc 0 ⌊L⌋₊) :
    wUniformCutoff M Z q r ≤ ⌈L ^ 2 / M * Z⌉₊ := by
  obtain ⟨hq0, hqL⟩ := mem_Ioc.mp hq
  obtain ⟨hr0, hrL⟩ := mem_Ioc.mp hr
  have hl : q.lcm r ≤ q * r := by
    calc
      q.lcm r ≤ q.gcd r * q.lcm r :=
        Nat.le_mul_of_pos_left _ (Nat.gcd_pos_of_pos_left r hq0)
      _ = q * r := Nat.gcd_mul_lcm q r
  have hqr : (q.lcm r : ℝ) ≤ L ^ 2 := by
    calc
      (q.lcm r : ℝ) ≤ (q * r : ℕ) := Nat.cast_le.mpr hl
      _ ≤ L * L := by
        rw [Nat.cast_mul]
        exact mul_le_mul
          ((Nat.cast_le.mpr hqL).trans (Nat.floor_le hL))
          ((Nat.cast_le.mpr hrL).trans (Nat.floor_le hL)) (Nat.cast_nonneg _) hL
      _ = L ^ 2 := (pow_two L).symm
  exact Nat.ceil_mono
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hqr hM.le) hZ)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
