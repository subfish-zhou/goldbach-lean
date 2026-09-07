import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLargeSupport
import Mathlib.Analysis.PSeries

/-!
# Finite density of large square divisors

The union over square divisors has an exact finite range and a floor-sum
majorant. The elementary inverse-square tail gives the uniform constant
`2`, including cutoffs below one and empty intervals.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

/-- Positive integers at most `T` with a square divisor whose root exceeds `Z`. -/
def largeSquareDivisorSet (T : ℕ) (Z : ℝ) : Finset ℕ := by
  classical
  exact (Ioc 0 T).filter (fun n => ∃ b : ℕ, Z < (b : ℝ) ∧ b ^ 2 ∣ n)

/-- The square-root upper endpoint and the floor lower endpoint are exact. -/
theorem largeSquareDivisorSet_eq_biUnion (T : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    largeSquareDivisorSet T Z =
      (Ioc ⌊Z⌋₊ T.sqrt).biUnion (fun b => (Ioc 0 T).filter (fun n => b ^ 2 ∣ n)) := by
  ext n
  simp only [largeSquareDivisorSet, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hn, b, hb, hbn⟩
    refine ⟨b, mem_Ioc.mpr ⟨(Nat.floor_lt hZ).mpr hb, ?_⟩, hn, hbn⟩
    exact Nat.le_sqrt'.mpr ((Nat.le_of_dvd (mem_Ioc.mp hn).1 hbn).trans
      (mem_Ioc.mp hn).2)
  · rintro ⟨b, hb, hn, hbn⟩
    exact ⟨hn, b, (Nat.floor_lt hZ).mp (mem_Ioc.mp hb).1, hbn⟩

/-- An exact integer floor-sum majorant, with no asymptotic endpoint convention. -/
theorem card_largeSquareDivisorSet_le_floor_sum (T : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    (largeSquareDivisorSet T Z).card ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, T / b ^ 2 := by
  rw [largeSquareDivisorSet_eq_biUnion T hZ]
  calc
    _ ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((Ioc 0 T).filter (fun n => b ^ 2 ∣ n)).card :=
      card_biUnion_le
    _ = _ := sum_congr rfl (fun b _ => Nat.Ioc_filter_dvd_card_eq_div T (b ^ 2))

/-- A uniform reciprocal-square estimate retains the natural floor at the cutoff. -/
theorem card_largeSquareDivisorSet_le_floor (T : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    ((largeSquareDivisorSet T Z).card : ℝ) ≤ 2 * T / ((⌊Z⌋₊ : ℝ) + 1) := by
  have htail :
      (∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((b : ℝ) ^ 2)⁻¹) ≤ 2 / ((⌊Z⌋₊ : ℝ) + 1) := by
    calc
      _ = ∑ b ∈ Ioo ⌊Z⌋₊ (T.sqrt + 1), ((b : ℝ) ^ 2)⁻¹ := by
        congr 1
        ext b
        simp only [mem_Ioc, mem_Ioo]
        omega
      _ ≤ _ := sum_Ioo_inv_sq_le _ _
  calc
    _ ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((T / b ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast card_largeSquareDivisorSet_le_floor_sum T hZ
    _ ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, (T : ℝ) / (b : ℝ) ^ 2 := by
      apply sum_le_sum
      intro b _
      exact_mod_cast (Nat.cast_div_le (m := T) (n := b ^ 2) (α := ℝ))
    _ = (T : ℝ) * ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((b : ℝ) ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_sum]
    _ ≤ (T : ℝ) * (2 / ((⌊Z⌋₊ : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg T)
    _ = _ := by ring

/-- Large square divisors have density at most `2 / Z` for every positive cutoff. -/
theorem card_largeSquareDivisorSet_le (T : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    ((largeSquareDivisorSet T Z).card : ℝ) ≤ 2 * T / Z := by
  calc
    _ ≤ 2 * T / ((⌊Z⌋₊ : ℝ) + 1) := card_largeSquareDivisorSet_le_floor T hZ.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hZ (Nat.lt_floor_add_one Z).le

/-- Real upper endpoints are truncated exactly before the density estimate. -/
theorem card_largeSquareDivisorSet_le_real {T Z : ℝ} (hT : 0 ≤ T) (hZ : 0 < Z) :
    ((largeSquareDivisorSet ⌊T⌋₊ Z).card : ℝ) ≤ 2 * T / Z := by
  calc
    _ ≤ 2 * (⌊T⌋₊ : ℝ) / Z := card_largeSquareDivisorSet_le ⌊T⌋₊ hZ
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.floor_le hT) (by positivity)) hZ.le

/-- Any supported factor above `Y` forces membership in the sparse square-divisor set. -/
theorem mem_largeSquareDivisorSet_of_large_support {n s d T : ℕ} {Y : ℝ}
    (hn : n ∈ Ioc 0 T) (hs : 0 < s) (hd : 0 < d) (hY : 0 ≤ Y)
    (hlarge : Y < (s : ℝ))
    (hsd : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) (hdsn : d * s ∣ n) :
    n ∈ largeSquareDivisorSet T (Real.sqrt Y) := by
  classical
  obtain ⟨b, hb, hsb, hbn⟩ :=
    exists_square_dvd_of_supported_mul_dvd hs hd hsd hdsn
  refine mem_filter.mpr ⟨hn, b, ?_, hbn⟩
  apply (Real.sqrt_lt hY (Nat.cast_nonneg b)).mpr
  exact hlarge.trans_le (by exact_mod_cast hsb)

/-- A uniform sparse envelope, even when the supported factor and `d` vary with `n`. -/
theorem card_largeSupport_le {T Y : ℝ} (hT : 0 ≤ T) (hY : 0 < Y)
    (S : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊T⌋₊)
    (hs : ∀ n ∈ S, ∃ s d : ℕ, 0 < s ∧ 0 < d ∧ Y < (s : ℝ) ∧
      (∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) ∧ d * s ∣ n) :
    (S.card : ℝ) ≤ 2 * T / Real.sqrt Y := by
  have hsub : S ⊆ largeSquareDivisorSet ⌊T⌋₊ (Real.sqrt Y) := by
    intro n hn
    obtain ⟨s, d, hs, hd, hlarge, hsd, hdsn⟩ := hs n hn
    exact mem_largeSquareDivisorSet_of_large_support (hS hn) hs hd hY.le hlarge hsd hdsn
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans
    (card_largeSquareDivisorSet_le_real hT (Real.sqrt_pos.mpr hY))

/-- The actual canonical `d₁` cutoff embeds in the same sparse envelope. -/
theorem wGCDData_mem_largeSquareDivisorSet (q r N₂ : ℕ) {N₁ T : ℕ} {Y : ℝ}
    (hN₁ : N₁ ∈ Ioc 0 T) (hY : 0 ≤ Y)
    (hlarge : Y < ((wGCDData q r N₁ N₂).d₁ : ℝ)) :
    N₁ ∈ largeSquareDivisorSet T (Real.sqrt Y) := by
  classical
  obtain ⟨b, hb, hsb, hbn⟩ :=
    wGCDData_exists_square_dvd_N₁ q r N₂ (mem_Ioc.mp hN₁).1
  refine mem_filter.mpr ⟨hN₁, b, (Real.sqrt_lt hY (Nat.cast_nonneg b)).mpr ?_, hbn⟩
  exact hlarge.trans_le (by exact_mod_cast hsb)

/-- Ordered pairs with large canonical `d₁`, independently of the moduli `q,r`. -/
def largeSupportPairs (N : Finset ℕ) (Y : ℝ) : Finset (ℕ × ℕ) :=
  (N ×ˢ N).filter
    (fun p => Y < (supportedPart (p.1 / p.1.gcd p.2) (p.1.gcd p.2) : ℝ))

/-- The large-`d₁` pair set is contained in a sparse first-coordinate strip. -/
theorem largeSupportPairs_subset (N : Finset ℕ) {T : ℕ} {Y : ℝ}
    (hN : N ⊆ Ioc 0 T) (hY : 0 ≤ Y) :
    largeSupportPairs N Y ⊆ largeSquareDivisorSet T (Real.sqrt Y) ×ˢ N := by
  intro p hp
  obtain ⟨hpN, hpY⟩ := mem_filter.mp hp
  obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpN
  exact mem_product.mpr
    ⟨wGCDData_mem_largeSquareDivisorSet 0 0 p.2 (hN hp₁) hY hpY, hp₂⟩

/-- A finite pair-count input for Cauchy--Schwarz; no coefficient estimates enter. -/
theorem card_largeSupportPairs_le {T Y : ℝ} (hT : 0 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) :
    ((largeSupportPairs N Y).card : ℝ) ≤ 2 * T ^ 2 / Real.sqrt Y := by
  have hcard : (N.card : ℝ) ≤ T := by
    calc
      _ ≤ ((Ioc 0 ⌊T⌋₊).card : ℝ) := Nat.cast_le.mpr (card_le_card hN)
      _ = (⌊T⌋₊ : ℝ) := by simp
      _ ≤ T := Nat.floor_le hT
  calc
    _ ≤ ((largeSquareDivisorSet ⌊T⌋₊ (Real.sqrt Y)).card : ℝ) * (N.card : ℝ) := by
      exact_mod_cast (card_le_card (largeSupportPairs_subset N hN hY.le)).trans_eq
        (card_product _ _)
    _ ≤ (2 * T / Real.sqrt Y) * T :=
      mul_le_mul (card_largeSquareDivisorSet_le_real hT (Real.sqrt_pos.mpr hY)) hcard
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
