import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKSecondaryGrowth

/-! Actual occupied-block geometry with only the numerator scale enlarged. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Frequency and modulus retain their original bounds; the shift enters only
in the numerator bound. No change to the floor, mask, key or x = 4MT is made. -/
theorem directPayKSecondary_growth_data
    {Cscale x η M T R S : ℝ} (hscale : 1 ≤ Cscale)
    (hx : 4 ≤ x) (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hxMT : x = 4 * M * T)
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hRS : R * S ≤ x)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2 * T)
    {a : ℤ} (ha : |(a : ℝ)| ≤ Cscale * x) {F : ℕ} (hF : (F : ℝ) ≤ 2 * T)
    {K : WExtractedKey} (hK : K ∈ wExtractedKeyBox (x ^ η))
    {j : Fin 5 → ℕ} {positive : Bool} {b : ℕ} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M (x ^ η)) N (Ioc 0 ⌊R * S⌋₊)
        a (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) :
    (2 : ℝ) ^ j 0 ≤ 8 * x ^ (6 : ℕ) ∧
    (wGramSecondaryNumeratorMax a K F j : ℝ) ≤ 16 * Cscale * x ^ (9 : ℕ) ∧
    16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4 ≤
      16 * x ^ (4 : ℕ) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hscale0 : 0 ≤ Cscale := by linarith
  have hZ : 0 ≤ x ^ η := Real.rpow_nonneg hx0.le _
  have hZx : x ^ η ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hη1
  have hTx : 2 * T ≤ x := by nlinarith
  have hRx : R ≤ x := (le_mul_of_one_le_right hR0 hS).trans hRS
  have hSx : S ≤ x := (le_mul_of_one_le_left hS0 hR).trans hRS
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  obtain ⟨hk, hr, hs⟩ := directLocalScale_fullLevel_coordinates hN (by positivity) hR0 hS0 ht
  have hn := (directPaySecondary_n_bound hN hQ hNT ht).trans hTx
  have hD := (directLocalScale_key_bounds hZ hK).1
  have hDx : (K.D : ℝ) ≤ x ^ (3 : ℕ) := hD.trans (by gcongr)
  have hrs : (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 ≤ x :=
    (mul_le_mul hr hs (by positivity) hR0).trans hRS
  have hH := directLocalScale_floor_frequency_le hM0 hZ hN hQ ht
  have hHbound : (2 : ℝ) ^ j 0 ≤ 8 * x ^ (6 : ℕ) := by
    calc
      _ ≤ 8 * ((K.D : ℝ) * (2 : ℝ) ^ j 1 *
          ((2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4)) / M * x ^ η := by convert hH using 1; ring
      _ ≤ 8 * (x ^ (3 : ℕ) * x * x) / 1 * x := by gcongr; exact hk.trans hRS
      _ = _ := by ring
  have hb : (K.1.2.1 : ℝ) ≤ x := by
    have hh := (mem_wExtractedKeyBox_iff.mp hK).2.1
    exact ((Nat.cast_le.mpr hh).trans (Nat.floor_le hZ)).trans hZx
  have ha' : (a.natAbs : ℝ) ≤ Cscale * x := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    exact ha
  refine ⟨hHbound, ?_, ?_⟩
  · unfold wGramSecondaryNumeratorMax
    push_cast
    rw [pow_succ (2 : ℝ) (j 0)]
    calc
      _ ≤ (Cscale * x) * x * (8 * x ^ (6 : ℕ) * 2) * x := by
        gcongr
        exact (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (hF.trans hTx)
      _ = _ := by ring
  · calc
      _ ≤ 16 * x * x * x * x := by gcongr <;> first | exact hr.trans hRx | exact hs.trans hSx
      _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
