import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeC2

noncomputable section
open Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Encode the integer points of `[L,U)` in the existing `(lower,upper]`
prime family. Buffering the scale avoids deleting an integral left endpoint. -/
def g9PrimeHalfOpenInterval (T L U : ℝ) (hT : 3 ≤ T)
    (hTL : T ≤ L) (hLU : L ≤ U) (hUT : U ≤ (4/3 : ℝ)*T) : PrimeC2Interval where
  scale := (2/3 : ℝ)*T
  lower := (⌈L⌉ : ℝ)-1
  upper := (⌈U⌉ : ℝ)-1
  one_le_scale := by linarith
  scale_le_lower := by have := Int.le_ceil L; linarith
  lower_le_upper := by
    have h : (⌈L⌉ : ℝ) ≤ (⌈U⌉ : ℝ) := by exact_mod_cast Int.ceil_mono hLU
    linarith
  upper_le_twice := by have := Int.ceil_lt_add_one U; linarith

/-- Both endpoint conventions are exact, including integral L or U. -/
theorem mem_g9PrimeHalfOpenInterval (T L U : ℝ) (hT : 3 ≤ T)
    (hTL : T ≤ L) (hLU : L ≤ U) (hUT : U ≤ (4/3 : ℝ)*T) (n : ℕ) :
    let z := g9PrimeHalfOpenInterval T L U hT hTL hLU hUT
    n ∈ primeSWInterval z.lower z.upper ↔ L ≤ (n : ℝ) ∧ (n : ℝ) < U := by
  have hlo : (0 : ℝ) ≤ (⌈L⌉ : ℝ)-1 := by have := Int.le_ceil L; linarith
  have hhi : (0 : ℝ) ≤ (⌈U⌉ : ℝ)-1 := by have := Int.le_ceil U; linarith
  change n ∈ Ioc ⌊(⌈L⌉ : ℝ)-1⌋₊ ⌊(⌈U⌉ : ℝ)-1⌋₊ ↔ _
  rw [mem_Ioc, Nat.floor_lt hlo, Nat.le_floor_iff hhi]
  constructor
  · rintro ⟨hnL,hnU⟩
    have hzL : (⌈L⌉ : ℤ)-1 < (n : ℤ) := by exact_mod_cast hnL
    have hzU : (n : ℤ) ≤ (⌈U⌉ : ℤ)-1 := by exact_mod_cast hnU
    constructor
    · exact_mod_cast (Int.ceil_le.mp (show (⌈L⌉ : ℤ) ≤ (n : ℤ) by omega))
    · exact_mod_cast (Int.lt_ceil.mp (show (n : ℤ) < (⌈U⌉ : ℤ) by omega))
  · rintro ⟨hnL,hnU⟩
    have hzL : (⌈L⌉ : ℤ) ≤ (n : ℤ) := Int.ceil_le.mpr (by exact_mod_cast hnL)
    have hzU : (n : ℤ) < (⌈U⌉ : ℤ) := Int.lt_ceil.mpr (by exact_mod_cast hnU)
    constructor
    · exact_mod_cast (show (⌈L⌉ : ℤ)-1 < (n : ℤ) by omega)
    · exact_mod_cast (show (n : ℤ) ≤ (⌈U⌉ : ℤ)-1 by omega)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
