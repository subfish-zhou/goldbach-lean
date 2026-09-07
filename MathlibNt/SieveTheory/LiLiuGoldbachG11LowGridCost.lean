import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridSource
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridCost

open Finset
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The sharper actual quadratic grid bound fits the existing cubic-log budget.
Only this finite-cardinality bridge is new; the scalar error payments are reused. -/
theorem goldbachG11LowGridCost_card {N : ℕ} {ε ρ : ℝ} (hρ : 1 < ρ)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    ((goldbachG11LowGridUsed N ε ρ).card : ℝ) ≤
      (1/Real.log ρ+1)^3*Real.log (N : ℝ)^3 := by
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ
  have hfloor : (fouvryG9GridIndex ρ N : ℝ) ≤ Real.log (N : ℝ)/Real.log ρ :=
    Nat.floor_le (div_nonneg (by linarith) hlρ.le)
  have hlinear : (fouvryG9GridIndex ρ N : ℝ)+1 ≤
      (1/Real.log ρ+1)*Real.log (N : ℝ) := by
    calc
      _ ≤ Real.log (N : ℝ)/Real.log ρ + Real.log (N : ℝ) := add_le_add hfloor hlog
      _ = _ := by ring
  have hcardNat := (card_filter_le (goldbachG11GridUsed N ε ρ)
    (fun k => ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ))).trans (goldbachG11GridUsed_card hρ)
  have hcard : ((goldbachG11LowGridUsed N ε ρ).card : ℝ) ≤
      ((fouvryG9GridIndex ρ N : ℝ)+1)^2 := by exact_mod_cast hcardNat
  have hb : 1 ≤ (fouvryG9GridIndex ρ N : ℝ)+1 := by
    have h : (0 : ℝ) ≤ fouvryG9GridIndex ρ N := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^2 := hcard
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^3 := pow_le_pow_right₀ hb (by omega)
    _ ≤ ((1/Real.log ρ+1)*Real.log (N : ℝ))^3 := pow_le_pow_left₀ (by positivity) hlinear 3
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig