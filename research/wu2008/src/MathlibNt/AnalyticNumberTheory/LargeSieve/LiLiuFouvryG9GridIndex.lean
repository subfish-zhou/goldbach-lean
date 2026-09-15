import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9Reindex

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Natural logarithmic index, used only for bases greater than one. -/
def fouvryG9GridIndex (ρ t : ℝ) : ℕ := ⌊Real.log t / Real.log ρ⌋₊

theorem fouvryG9GridIndex_bounds {ρ t : ℝ} (hρ : 1 < ρ) (ht : 1 ≤ t) :
    ρ ^ fouvryG9GridIndex ρ t ≤ t ∧ t < ρ ^ (fouvryG9GridIndex ρ t + 1) := by
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hl : 0 < Real.log ρ := Real.log_pos hρ
  have hq : 0 ≤ Real.log t / Real.log ρ :=
    div_nonneg (Real.log_nonneg ht) hl.le
  constructor
  · apply (Real.log_le_log_iff (pow_pos hr _) ht0).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hl).mp (Nat.floor_le hq)
  · apply (Real.log_lt_log_iff ht0 (pow_pos hr _)).mp
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one (Real.log t / Real.log ρ))

theorem fouvryG9GridIndex_mono {ρ t N : ℝ} (hρ : 1 < ρ)
    (ht : 1 ≤ t) (htN : t ≤ N) :
    fouvryG9GridIndex ρ t ≤ fouvryG9GridIndex ρ N := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one ht) htN) (Real.log_pos hρ).le

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
