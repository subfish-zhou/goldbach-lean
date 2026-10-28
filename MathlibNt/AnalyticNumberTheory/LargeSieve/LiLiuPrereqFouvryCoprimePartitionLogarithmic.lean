import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCoprimePartition
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithmic cardinality bound for the Fouvry partition

The explicit absolute constant `4 / log 2` converts the exact binary count
to the bound in F87, Lemma 7. Real cutoffs are handled by the natural floor,
with the original integer-pair domain proved exactly.
-/

namespace LiLiuPrereqFouvry.CoprimePartition

noncomputable def partitionConstant : ℝ := 4 / Real.log 2

theorem partitionConstant_pos : 0 < partitionConstant := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

theorem bitColor_card_le_log {T : ℕ} (hT : 2 ≤ T) :
    (2 * (Nat.log2 T + 1) : ℕ) ≤ partitionConstant * Real.log T := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hnat : (Nat.log2 T : ℝ) ≤ Real.log T / Real.log 2 := Real.log2_le_logb T
  have hnat' := (le_div_iff₀ htwo).mp hnat
  have hbound : (2 * (Nat.log2 T + 1) : ℕ) * Real.log 2 ≤ 4 * Real.log T := by
    push_cast
    nlinarith
  rw [partitionConstant, div_mul_eq_mul_div]
  exact (le_div_iff₀ htwo).mpr hbound

theorem card_partition_le_log {T : ℕ} (hT : 2 ≤ T) (ω : ℕ) :
    ((partition T ω).card : ℝ) ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) := by
  calc
    ((partition T ω).card : ℝ) ≤ ((2 * (Nat.log2 T + 1)) ^ (ω ^ 2) : ℕ) := by
      exact_mod_cast card_partition_le T ω
    _ ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast bitColor_card_le_log hT) _


noncomputable def realPartition (T : ℝ) (ω : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  partition ⌊T⌋₊ ω


theorem card_realPartition_le_log {T : ℝ} (hT : 2 ≤ T) (ω : ℕ) :
    ((realPartition T ω).card : ℝ) ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) := by
  have hT₀ : 0 ≤ T := by linarith
  have hfloor : 2 ≤ ⌊T⌋₊ := (Nat.le_floor_iff hT₀).mpr (by exact_mod_cast hT)
  have hfloor₀ : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast (by omega : 0 < ⌊T⌋₊)
  calc
    ((realPartition T ω).card : ℝ) ≤
        (partitionConstant * Real.log (⌊T⌋₊ : ℝ)) ^ (ω ^ 2) :=
      card_partition_le_log hfloor ω
    _ ≤ _ := pow_le_pow_left₀
      (mul_nonneg partitionConstant_pos.le (Real.log_natCast_nonneg _))
      (mul_le_mul_of_nonneg_left (Real.log_le_log hfloor₀ (Nat.floor_le hT₀))
        partitionConstant_pos.le) _


end LiLiuPrereqFouvry.CoprimePartition
